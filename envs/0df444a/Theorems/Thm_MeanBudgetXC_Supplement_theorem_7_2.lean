-- Prove2me | Theorems.Thm_MeanBudgetXC_Supplement_theorem_7_2
-- name    : MeanBudgetXC.Supplement.theorem_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:18:17.104193+00:00
-- url     : https://prove2.me/theorems/f3337390-f643-41cf-b35a-e7ade8d6ddf3
-- title:
--   Theorem 7.2 — distinguishing $V(u)=1$ from $V(u)\ge1+\delta_\theta$ on sparse binary caps is NP-hard
-- statement:
--   For a graph $F$ on $[N]$ let $u_F=\mathbf 1_{E(F)}$ be its binary cap, and let $V_A(u)=\max\{1^{\mathsf T}q:q\in A,\ 0\le q\le u\}$. Fix a rational $\theta\in(0,1)$. There are constants $\delta_\theta>0$, $D_\theta$ and $E_\theta$ such that, for the family of graphs $F$ on $[N]$ that have an edge, are triangle-free, and satisfy $\Delta(F)\le D_\theta$, $|E(F)|\le E_\theta N$ and $\Delta(F)\le\lfloor\theta N\rfloor-1$, encoded by their full $M$-bit caps:
--
--   1. for every fixed activity $a\ge2$, it is NP-hard under deterministic polynomial-time reductions to distinguish
--   $$V_{P^{(a)}_{N,\lfloor\theta N\rfloor}}(u_F)=1\qquad\text{from}\qquad V_{P^{(a)}_{N,\lfloor\theta N\rfloor}}(u_F)\ge1+\delta_\theta;$$
--   2. for every fixed rational $B>2$ and every $a\ge2$, the same holds for $P^{(a;B)}_{N,\lfloor\theta N\rfloor}$ with gap $\min\{\delta_\theta,(B-2)/2\}$;
--   3. at $B=2$, every query of the family has value one: $V_{P^{(a;2)}_{N,\lfloor\theta N\rfloor}}(u_F)=1$ for every $a\ge2$.
--
--   NP-hardness means: for every NP language $L$ over a finite nonempty alphabet there is a polynomial-time computable map sending members of $L$ to codes of instances of value one and non-members to codes of instances of value at least one plus the gap.
--
--   So, unless P = NP, no polynomial-time algorithm answers binary capacity queries to within half the gap, although at budget two (item 3) every such query is trivial.
--
--   **Formalization Note** NP, polynomial-time computability and the machine model are the platform's `CookPvsNP` definitions. Instances are encoded as $N$ in unary, a separator, and the $\binom N2$ bits of $u_F$ in lexicographic order.
--
--   Differences from the source:
--   - encoding: the vertex set $[N]$ → `Fin N`; reason: the same set, indexed from zero
--   - encoding: $V_A(u)=\max\{1^{\mathsf T}q: q\in A,\ 0\le q\le u\}$ → `capValue A u`, the supremum of $\sum_e q_e$ over the capped set; reason: the capped set is nonempty and lies in the box $[0,u]$, and $A$ is a polyhedron or a compact body, so the supremum is attained and equals the maximum
--   - reading: "binary caps with triangle-free support of maximum degree $D_\theta$ and $O_\theta(N)$ edges" and "this same nonempty sparse-support family" → graphs $F$ with an edge, triangle-free, $\Delta(F)\le D_\theta$, $|E(F)|\le E_\theta N$ for a constant $E_\theta$ chosen with $D_\theta$, and $\Delta(F)\le\lfloor\theta N\rfloor-1$; reason: "maximum degree $D_\theta$" is a bound; $O_\theta(N)$ edges is a constant depending on $\theta$; the last condition is the reduction's family in the proof idea ("with $\Delta(F)\le d-1$", p.36), and the value identity (60) of Appendix F.2 behind the $B=2$ clause requires it
--   - encoding: NP-hard under deterministic polynomial-time reductions to distinguish two value ranges → `PromiseNPHard YES NO`: every `CookPvsNP.NP` language over a finite nonempty alphabet has a `CookPvsNP.PolyTimeComputable` map into YES on members and into NO on non-members; reason: this is many-one NP-hardness of a promise problem in the platform's machine model
--   - encoding: an instance $(N,u_F)$ as input to an algorithm → the binary string of $N$ in unary, a separator and the $\binom N2$ bits of $u_F$; reason: the full-cap encoding the paper mentions ("The full cap has $O(N^2)$ bits", p.36); it is injective
--   - reading: "At $B=2$, every query in this same nonempty sparse-support family has value one" → $V_{P^{(a;2)}_{N,\lfloor\theta N\rfloor}}(u_F)=1$ for every $a\ge2$ and every $F$ of the family; reason: the sentence follows the clause on $P^{(a;B)}$ for every fixed activity $a\ge2$
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c712270634eb9c25e965df506f4fd2cfa5c228f4bb13f3ca9ddc9859e76), Theorem 7.2, p.36; family from its proof idea, p.36, and Appendix F.2, pp.49–50

import Mathlib
import Definitions.Def_MeanBudgetXC_pairBody
import Definitions.Def_MeanBudgetXC_budgetBody
import Definitions.Def_MeanBudgetXC_Supplement_binaryQueryLang
import Definitions.Def_MeanBudgetXC_Supplement_PromiseNPHard

namespace MeanBudgetXC.Supplement

/-- **Theorem 7.2** (Binary query hardness) (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Theorem 7.2, p.36). Fix rational
`θ ∈ (0, 1)`. There are constants `δ_θ > 0` and `D_θ` such that, for every fixed activity `a ≥ 2`, it
is NP-hard under deterministic polynomial-time reductions to distinguish
`V_{P^{(a)}_{N,⌊θN⌋}}(u) = 1` from `V_{P^{(a)}_{N,⌊θN⌋}}(u) ≥ 1 + δ_θ`, even for binary caps with
triangle-free support of maximum degree `D_θ` and `O_θ(N)` edges. For every fixed rational
`B > 2`, the same assertion holds for `P^{(a;B)}` with gap `min{δ_θ, (B − 2)/2}`. At `B = 2`, every
query in this same nonempty sparse-support family has value one.

**Formalization Note** The instances are binary caps `u_F = 1_{E(F)}` for graphs `F` on `[N]` in
`IsSparseFamily θ D_θ E_θ`: nonempty, triangle-free, `Δ(F) ≤ D_θ`, `|E(F)| ≤ E_θ N` (`E_θ` is the
constant of "`O_θ(N)` edges"), and `Δ(F) ≤ ⌊θN⌋ − 1`. The last condition is the reduction's family
in the proof idea (p.36) and Appendix F.2, where the value identity (60) needs it. An instance is
encoded as `graphCode N F` (the full `M`-bit cap, p.36). NP-hardness of the gap problem is
`PromiseNPHard YES NO`: a `CookPvsNP` polynomial-time map from every NP language sends members
into YES (value one) and non-members into NO (value at least one plus the gap). `δ_θ, D_θ, E_θ` are
chosen after `θ` and before `a` and `B`. -/
theorem theorem_7_2 :
    ∀ θ : ℚ, 0 < θ → θ < 1 → ∃ δ : ℝ, 0 < δ ∧ ∃ Dθ Eθ : ℕ, ∀ a : ℕ, 2 ≤ a →
      PromiseNPHard
          (binaryQueryLang θ Dθ Eθ (fun N => pairBody (Fin N) ⌊(θ : ℝ) * N⌋₊ a) (fun v => v = 1))
          (binaryQueryLang θ Dθ Eθ (fun N => pairBody (Fin N) ⌊(θ : ℝ) * N⌋₊ a)
            (fun v => 1 + δ ≤ v)) ∧
      (∀ B : ℚ, 2 < B →
        PromiseNPHard
          (binaryQueryLang θ Dθ Eθ (fun N => budgetBody (Fin N) ⌊(θ : ℝ) * N⌋₊ a B)
            (fun v => v = 1))
          (binaryQueryLang θ Dθ Eθ (fun N => budgetBody (Fin N) ⌊(θ : ℝ) * N⌋₊ a B)
            (fun v => 1 + min δ (((B : ℝ) - 2) / 2) ≤ v))) ∧
      ∀ (N : ℕ) (F : SimpleGraph (Fin N)) [DecidableRel F.Adj], IsSparseFamily θ Dθ Eθ F →
        capValue (budgetBody (Fin N) ⌊(θ : ℝ) * N⌋₊ a 2) (binaryCap F) = 1 := by sorry

end MeanBudgetXC.Supplement
