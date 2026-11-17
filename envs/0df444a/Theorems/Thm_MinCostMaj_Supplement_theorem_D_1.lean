-- Prove2me | Theorems.Thm_MinCostMaj_Supplement_theorem_D_1
-- name    : MinCostMaj.Supplement.theorem_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:41:18.910761+00:00
-- url     : https://prove2.me/theorems/298bef8d-7c22-4c90-8700-269c138ea048
-- title:
--   Theorem D.1 — under the UGC, $\mathrm{cUG}(k)$ has no polynomial-time constant-factor approximation for any fixed $k\ge2$
-- statement:
--   Fix $k\ge2$ and write $[k]=\{0,\dots,k-1\}$ and $Z_k=\{(a,a+1 \bmod k) : a\in[k]\}$. An instance of $\mathrm{cUG}(k)$ is a directed graph $G=(V,E)$ with at least one arc; loops are allowed. An assignment $\beta:V\to[k]$ pays $1$ on each arc $(u,v)\in E$ with $(\beta(u),\beta(v))\notin Z_k$ and $0$ otherwise. Write $\mathrm{cost}_G(\beta)$ for the total cost and $\mathrm{OPT}(G)=\min_\beta \mathrm{cost}_G(\beta)$.
--
--   Assume the Unique Games Conjecture. Let $C$ be any real constant. Suppose a deterministic polynomial-time algorithm outputs, on every such instance $G$, an assignment $\beta$ with
--   $$\mathrm{cost}_G(\beta)\le C\cdot \mathrm{OPT}(G).$$
--   Then $\mathsf P=\mathsf{NP}$.
--
--   Equivalently, assuming the UGC and $\mathsf P\neq\mathsf{NP}$, no fixed-alphabet cyclic Unique Games deletion problem admits a polynomial-time constant-factor approximation. This is the hardness side of the dichotomy of Theorem 1.1. When $\mathrm{cUG}(k)$ reduces to $\mathrm{MinCostCSP}(\mathbf A)$, the second alternative of Theorem 1.1 is a genuine obstruction to constant-factor approximation, not merely a different case.
--
--   **Formalization Note** The UGC is the published `OptInapprox.MaxCut.UGC`, and $\mathsf P$, $\mathsf{NP}$ are the published `CookPvsNP` classes over every finite alphabet. The conclusion is stated as $\mathsf{NP}\subseteq\mathsf P$, which together with $\mathsf P\subseteq\mathsf{NP}$ is $\mathsf P=\mathsf{NP}$. Instances are the published weighted `CUGInst` restricted to well-formed instances with every weight $1$, no repeated arc, and at least one arc. The cost is the published unnormalized `CUGInst.cost`. The algorithm is a TM2 machine on the published encodings `encCUG` and `encList`, as in the published `CUGReducesTo`.
--
--   Differences from the source:
--   - reading: Assume the UGC. Then … cUG(k) admits no polynomial-time constant-factor approximation algorithm → UGC → (a polynomial-time C-approximation on the instances → NP ⊆ P over every finite alphabet); reason: the printed statement leaves P ≠ NP implicit; the proof concludes "NP-hard to approximate cUG(k) within any constant factor" (p.30) and p.3 writes "assuming P≠NP and the UGC"; without it the statement is unprovable, because the UGC is consistent with P = NP
--   - encoding: the UGC, P and NP → the published OptInapprox.MaxCut.UGC and the CookPvsNP classes P Sym, NP Sym for every finite alphabet Sym; reason: the UGC states NP-hardness in that model, so one model is used for every class in the statement
--   - reading: a polynomial-time algorithm → a deterministic TM2 machine (Turing.TM2ComputableInPolyTime) from encCUG G to encList of the values β(0), …, β(n−1); reason: the paper names no machine model; this is the convention of the published CUGReducesTo; the theorem says "polynomial-time", not "randomized"
--   - reading: an instance of cUG(k) is a directed graph G = (V, E) with every arc of cost 1 → a well-formed CUGInst with every arc weight 1, no two arcs with the same (u, v), at least one arc, and loops allowed; reason: E is a set of arcs, and the normalized cost divides by |E|, so |E| ≥ 1; the algorithm is assumed only on these instances, which is the strong form
--   - encoding: normalized cost cost_G(α) = (1/|E|) Σ cost_(u,v)(α) → the published unnormalized CUGInst.cost; reason: |E| > 0 multiplies both sides of cost ≤ C·OPT, so a C-approximation for one is a C-approximation for the other
--   - encoding: constant-factor approximation → for every real C fixed before the instances, cost_G(β) ≤ C · OPT(G) on every instance; reason: the standard multiplicative guarantee for a minimization problem
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667, Theorem D.1, p.30 (PDF p.31); instances and cost: Appendix D, pp.27–28 (PDF pp.28–29); proof: §§D.1–D.3, pp.28–30 (Lemma "SDP solution for an inconsistent cycle", p.29)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_MinCostMaj_CUGInst
import Definitions.Def_MinCostMaj_encInst

namespace MinCostMaj.Supplement

open MinCostMaj

/-- **Theorem D.1 (inapproximability of cUG(k) under the UGC).**

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, Appendix D, §D.3, Theorem D.1, p.30 (PDF p.31): "Assume the UGC.
Then, for every fixed k ≥ 2, cUG(k) admits no polynomial-time constant-factor approximation
algorithm." The proof ends: "Consequently, it is NP-hard to approximate cUG(k) within any constant
factor." Instances (Appendix D, pp.27–28): "An instance of cUG(k) is a directed graph G = (V, E).
The cost incurred by an assignment α : V → [k] on an edge (u, v) is 0 if (α(u), α(v)) ∈ Z_k,
1 otherwise", with normalized cost `cost_G(α) = (1/|E|) Σ_{(u,v)∈E} cost_{(u,v)}(α)`.

Assume the Unique Games Conjecture. Let `k ≥ 2` and let `C` be any real constant. If a
deterministic polynomial-time machine `alg` outputs, on every unweighted cUG(k) instance `G`
(a directed graph with at least one arc), an assignment `β : V → [k]` with
`cost_G(β) ≤ C · OPT(G)`, then `P = NP` (over every finite alphabet).

**Formalization Note.**
* The UGC is the published `OptInapprox.MaxCut.UGC` (Khot's conjecture [45] as gap NP-hardness of
  Unique Label Cover); `P`, `NP` are the published `CookPvsNP` classes, the model in which that UGC
  states NP-hardness. "No algorithm unless P = NP" is stated as its contrapositive: such an algorithm
  gives `NP ⊆ P` over every finite alphabet (equivalent to `P = NP`, since `P ⊆ NP`). The printed
  statement leaves `P ≠ NP` implicit; the proof's conclusion "NP-hard to approximate" and p.3's
  "assuming P≠NP and the UGC" make it explicit.
* "Polynomial-time" (deterministic, as printed) is Mathlib's `Turing.TM2ComputableInPolyTime` on
  the published encodings `encCUG` (instance) and `encList` (assignment as the list of values
  `β(0), …, β(n−1)`), the convention of the published `CUGReducesTo`.
* Instances are the published `CUGInst` restricted to Appendix D's graphs: well-formed, every arc
  of weight `1`, no repeated arc `(u, v)` (`E` is a set), and at least one arc (the normalized cost
  divides by `|E|`). Loops `(u, u)` are allowed. The algorithm is assumed to work only on these
  instances, the strong form of the statement.
* The published `CUGInst.cost` is the unnormalized cost `|E| · cost_G`; a factor-`C` guarantee is
  the same for both, since `|E| > 0` multiplies both sides.
* `C` is any real number, fixed before the instances; for `OPT(G) = 0` the guarantee asks for an
  optimal assignment. -/
theorem theorem_D_1 :
    OptInapprox.MaxCut.UGC →
      ∀ k : ℕ, 2 ≤ k → ∀ C : ℝ, ∀ alg : CUGInst → List ℕ,
        Nonempty (Turing.TM2ComputableInPolyTime encCUG encList alg) →
        (∀ G : CUGInst, G.WellFormed → (∀ e ∈ G.arcs, e.2.2 = 1) →
            (G.arcs.map fun e => (e.1, e.2.1)).Nodup → G.arcs ≠ [] →
            ∃ β : Fin G.n → Fin k, alg G = List.ofFn (fun u => (β u : ℕ)) ∧
              G.cost k β ≤ C * G.OPT k) →
        ∀ (Sym : Type) [Fintype Sym], CookPvsNP.NP Sym ⊆ CookPvsNP.P Sym := by sorry

end MinCostMaj.Supplement
