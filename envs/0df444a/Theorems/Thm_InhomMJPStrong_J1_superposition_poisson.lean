-- Prove2me | Theorems.Thm_InhomMJPStrong_J1_superposition_poisson
-- name    : InhomMJPStrong.J1.superposition_poisson
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:49.016129+00:00
-- url     : https://prove2.me/theorems/d1c78557-5452-4602-88e3-c0bc2d3c1a1e
-- title:
--   Step (1), p. 6 — independent superpositions have rate n
-- statement:
--   Let the independent clocks of Step (1) have base rate $\lambda_0\ge1$, and let $n\ge\lambda_0$. Superpose the base clock with the unit-rate clocks indexed by $\lambda_0+1,\ldots,n$, separately for the inspection and observation grids. The successive gaps of each resulting grid are mutually independent and each has the exponential law of rate $n$:
--
--   $$
--   \chi^{(n)}_{\ell+1}-\chi^{(n)}_\ell\sim\operatorname{Exp}(n),
--   \qquad
--   \theta^{(n)}_{\ell+1}-\theta^{(n)}_\ell\sim\operatorname{Exp}(n).
--   $$
--
--   This identifies the two superpositions as the rate-$n$ Poisson processes used throughout the approximation.
--
--   **Formalization Note** The statement includes $n=\lambda_0$, where the superposition has no extra clocks and equals the base clock; Theorem 1 of the paper uses this boundary case.
-- source:
--   Bladt & Peralta, Strongly convergent homogeneous approximations to inhomogeneous Markov jump processes and applications, arXiv:2204.02954v3, p. 6, Step (1), paragraph following (4)

import Mathlib
import Definitions.Def_InhomMJPStrong_J1_Model

namespace InhomMJPStrong.J1

open MeasureTheory ProbabilityTheory

/-- Step (1), p. 6: each superposition is a rate-n Poisson process. -/
theorem superposition_poisson {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Src → Ω → ℝ)
    (rate n : ℕ) (hrate : 1 ≤ rate) (hn : rate ≤ n)
    (hX : IsUnifSetup rate X P) :
    iIndepFun (fun l ω => chi rate n X ω (l + 1) - chi rate n X ω l) P ∧
    (∀ l, HasLaw (fun ω => chi rate n X ω (l + 1) - chi rate n X ω l)
      (expMeasure (n : ℝ)) P) ∧
    iIndepFun (fun l ω => theta rate n X ω (l + 1) - theta rate n X ω l) P ∧
    (∀ l, HasLaw (fun ω => theta rate n X ω (l + 1) - theta rate n X ω l)
      (expMeasure (n : ℝ)) P) := by sorry

end InhomMJPStrong.J1
