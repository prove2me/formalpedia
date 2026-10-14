-- Prove2me | Theorems.Thm_OAI_PiExponent_denominator_clearing_determinant_dichotomy
-- name    : OAI.PiExponent.denominator_clearing_determinant_dichotomy
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-14T08:31:29.391427+00:00
-- url     : https://prove2.me/theorems/f47bd5c2-75c5-40be-b6b3-bcce42277bd1
-- title:
--   Denominator clearing forces a determinant obstruction alternative
-- statement:
--   Under the exact approximation, weight, and eventual jet-surjectivity hypotheses, denominator clearing and the determinant estimates force either the error-side bound or the collision-side bound. Each alternative contradicts a strict margin in the determinant budget.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_DeterminantSetup

theorem OAI.PiExponent.denominator_clearing_determinant_dichotomy
    (nu : ℝ) (hnu : 2 < nu) (B : OAI.PiExponent.DeterminantBudget nu)
    (p : Fin B.m → ℤ) (q w : Fin B.m → ℕ)
    (hq : ∀ i, 2 ≤ q i) (hp : ∀ i, p i ≠ 0)
    (hw : ∀ i, w i = Nat.ceil (Real.log (q i : ℝ)))
    (hmin : ∀ i, B.wmin ≤ w i)
    (happrox : ∀ i,
      |Real.pi - (p i : ℝ) / (q i : ℝ)| ≤ (q i : ℝ) ^ (-nu))
    (hrank : ∀ c : Fin B.K → Fin B.m → ℂ,
      (∀ i : Fin B.m, Function.Injective (fun j : Fin B.K => c j i)) →
      OAI.PiExponent.eventualLogJetSurjective
        B.m B.K B.w0 B.v0 B.theta w c) :
    nu * (B.A * (1 - B.eta) - (B.theta : ℝ)) -
        (1 - (B.theta : ℝ)) ≤ B.E ∨
      (Real.log 2 / 4) *
        (B.eta ^ 2 * (B.K : ℝ) * (B.theta : ℝ) ^ B.m /
          (((B.m : ℝ) + 1) * (B.v0 : ℝ) * B.A ^ B.m)) ≤ 1 + B.E := by sorry
