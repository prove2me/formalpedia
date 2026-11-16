-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gammaLevyExponent
-- name    : Kyprianou.Ch01.gammaLevyExponent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:10:14.359465+00:00
-- url     : https://prove2.me/theorems/32009c4f-2a5e-4668-b3b2-28639144a632
-- title:
--   §1.2.4: gamma Lévy measure and complex characteristic exponent
-- statement:
--   The source's explicit gamma jump law Π(dx)=β e^(−αx)dx/x is an admissible Lévy measure of infinite mass. For every real frequency θ, the compensated exponent integral equals β log(1−iθ/α). Its proof is an application of the full complex Frullani lemma, with the truncation drift correctly adjusted. This remains an uncompiled draft theorem.
-- source:
--   Kyprianou (2006), Chapter 1, §1.2.4, pp. 7–8.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.gammaLevyExponent
    (alpha beta : ℝ) (ha : 0 < alpha) (hb : 0 < beta) :
    IsLevyMeasure (gammaLevyMeasure alpha beta) ∧
      gammaLevyMeasure alpha beta Set.univ = ⊤ ∧
      ∀ theta : ℝ,
        IntegrableOn (fun x : ℝ =>
          ((1 : ℂ) - Complex.exp (Complex.I * (theta : ℂ) * (x : ℂ))) *
            ((beta : ℂ) * Complex.exp (-(alpha : ℂ) * (x : ℂ)) / (x : ℂ)))
          (Set.Ioi (0 : ℝ)) ∧
        (∫ x in Set.Ioi (0 : ℝ),
          ((1 : ℂ) - Complex.exp (Complex.I * (theta : ℂ) * (x : ℂ))) *
            ((beta : ℂ) * Complex.exp (-(alpha : ℂ) * (x : ℂ)) / (x : ℂ))
          ∂volume) =
            (beta : ℂ) *
              Complex.log (1 - Complex.I * (theta : ℂ) / (alpha : ℂ)) := by
  sorry
