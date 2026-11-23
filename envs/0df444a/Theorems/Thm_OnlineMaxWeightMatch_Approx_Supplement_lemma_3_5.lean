-- Prove2me | Theorems.Thm_OnlineMaxWeightMatch_Approx_Supplement_lemma_3_5
-- name    : OnlineMaxWeightMatch.Approx.Supplement.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:29:01.767626+00:00
-- url     : https://prove2.me/theorems/fe1af34d-5a0d-4a6c-9c48-17d7fd635d56
-- title:
--   Lemma 3.5, p. 8 — the clause-ball gain of $OPT_{on}$ is $\frac{(1-m^{-4})^{m-1}}{2k}OPT_{on}(\phi)+\delta$ with $\delta\in[0,2m^{-1}]$
-- statement:
--   Let $\phi$ be a 3CNF MAX-SSAT formula with $n$ variables and $m$ clauses, in which no random variable appears negated and every variable appears in at most $k$ clauses, and let $\mathcal I_\phi$ be the RideHail instance of §3.2. Let $\pi$ be an optimal online algorithm on $\mathcal I_\phi$, and let $B$ be its gain from the clause balls. Then for some $\delta\in[0,2m^{-1}]$,
--   $$\mathbb E[B]=\frac{(1-m^{-4})^{m-1}}{2k}\cdot OPT_{on}(\phi)+\delta.$$
--
--   Together with Lemma 3.4 this gives $OPT_{on}(\mathcal I_\phi)$ as an explicit affine function of $OPT_{on}(\phi)$ up to an error in $[0,2/m]$. Theorem 1.1 uses it to transfer approximations of $OPT_{on}(\mathcal I_\phi)$ to $OPT_{on}(\phi)$.
--
--   **Formalization Note** The statement holds for every optimal deterministic policy. For $m=0$ there is no clause ball, both sides are $0$ and Lean's $0^{-1}=0$ forces $\delta=0$.
--
--   Differences from the source:
--
--   - generalization: φ as in Lemma 3.1 with its constant k → any 3CNF φ with no negated random variable and every variable in at most k clauses, for any k used as the gadget parameter; reason: the lemma is stated for the instances and the constant of Lemma 3.1; it holds for every such k
--   - generalization: "without loss of generality, suppose n is even" → any number n of variables; reason: the construction and the argument do not use the parity of n; even n is a special case
--   - reading: "B the gain of OPT_on from clause balls" → for every optimal deterministic policy π, the expected profit of π from the balls n+1, …, n+m; reason: OPT_on denotes an optimal online algorithm, not a fixed one; the statement holds for each
--   - encoding: m^{-1}, m^{-4} for m ≥ 1 → Lean inverses, with 0^{-1} = 0 at m = 0; reason: at m = 0 both sides are 0 and δ = 0; no instance with m ≥ 1 changes
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 8, Lemma 3.5 (construction §3.2, pp. 7–8)

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Supplement_Gadget

namespace OnlineMaxWeightMatch.Approx.Supplement

open OnlineMaxWeightMatch.Approx

/-- Lemma 3.5: for every optimal online policy on `I_φ`, its expected gain `𝔼[B]` from clause
balls equals `((1 - m^{-4})^{m-1} / (2k)) · OPT_on(φ) + δ` for some `δ ∈ [0, 2/m]`. -/
theorem lemma_3_5 (φ : SSATFormula) (k : ℕ) (hφ : φ.IsThreeCNF) (h1 : φ.NoNegatedRandom)
    (h2 : φ.OccursAtMost k)
    (π : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length))
    (hπ : policyValue (gadget φ k) π = optOn (gadget φ k)) :
    ∃ δ : ℝ, 0 ≤ δ ∧ δ ≤ 2 * ((φ.clauses.length : ℝ))⁻¹ ∧
      clauseGain φ k π =
        (1 - ((φ.clauses.length : ℝ) ^ 4)⁻¹) ^ (φ.clauses.length - 1) / (2 * k) * ssatOpt φ
          + δ := by sorry

end OnlineMaxWeightMatch.Approx.Supplement
