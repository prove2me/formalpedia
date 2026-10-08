-- Prove2me | Theorems.Thm_GoldieRenewal_Kesten_ladder_lower_bound
-- name    : GoldieRenewal.Kesten.ladder_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:10:43.764152+00:00
-- url     : https://prove2.me/theorems/f2523744-026b-40a9-9105-d3cbcd01d174
-- title:
--   Proof of Theorem 4.1, p. 157 — P(|Π_n| > e^t for some n ≥ 1) ≥ δe^{−κt} for all large t
-- statement:
--   Let $M_1,M_2,\dots$ be independent real random variables, each with a law satisfying the conditions of Lemma 2.2 for some $\kappa>0$ ($\mathbf E|M|^\kappa=1$, $\mathbf E|M|^\kappa\log^+|M|<\infty$, $\log|M|$ given $M\neq0$ nonarithmetic), and let $\Pi_n=M_1\cdots M_n$. Then there is $\delta>0$ such that
--
--   $$
--   P\big(|\Pi_n|>e^t\ \text{for some } n\ge1\big)\ \ge\ \delta\,e^{-\kappa t}\qquad\text{for all sufficiently large } t .
--   $$
--
--   Equivalently, the supremum of the random walk $V_n=\log|\Pi_n|$, whose steps $\log|M_k|$ have negative mean and may equal $-\infty$, exceeds $t$ with probability at least of order $e^{-\kappa t}$. This is the Cramér–Lundberg lower bound used in the proof of Theorem 4.1 to show $C_++C_->0$.
--
--   **Formalization Note** The sequence is stored 0-based in Lean. The paper obtains the bound from an exact asymptotic (9.28) for $P(\sup_nV_n>t)$; only the lower bound is stated, because the constant printed in (9.28) is doubtful.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 157, proof of Theorem 4.1, unnumbered (before (9.28))

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Kesten_Perpetuity

namespace GoldieRenewal.Kesten

open MeasureTheory ProbabilityTheory Filter

/-- **The ladder lower bound** (Goldie, *Implicit renewal theory and tails of solutions of random
equations*, Ann. Appl. Probab. 1(1) (1991), p. 157, proof of Theorem 4.1, unnumbered: "it
suffices to show `P(|Π_n| > e^t for some n ≥ 1)` is at least `δe^{−κt}` for all large `t`, where
`δ > 0`"). Let `M₁, M₂, …` be independent, each with law `ν` satisfying the conditions of
Lemma 2.2 for `κ`, and `Π_n = M₁ ⋯ M_n`. Then there is `δ > 0` such that, for all sufficiently
large `t`, `P(|Π_n| > e^t for some n ≥ 1) ≥ δ e^{−κt}`.

**Formalization Note** The sequence is stored 0-based (`M i` is the paper's `M_{i+1}`, and
`piProd M n = M₁ ⋯ M_n`). The paper derives this from (9.28) (Feller's Cramér–Lundberg
asymptotic); only the lower bound is stated here, since the printed constant of (9.28) is
doubtful. -/
theorem ladder_lower_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (κ : ℝ) (ν : Measure ℝ) (hν : GoldieRenewal.Implicit.CramerConditions κ ν)
    (M : ℕ → Ω → ℝ) (hM : ∀ i, Measurable (M i)) (hindep : iIndepFun M P)
    (hlaw : ∀ i, P.map (M i) = ν) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ t : ℝ in atTop,
      δ * Real.exp (-κ * t) ≤ P.real {ω | ∃ n : ℕ, 1 ≤ n ∧ Real.exp t < |piProd M n ω|} := by sorry

end GoldieRenewal.Kesten
