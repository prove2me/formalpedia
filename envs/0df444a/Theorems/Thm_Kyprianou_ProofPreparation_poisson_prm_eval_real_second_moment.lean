-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_real_second_moment
-- name    : Kyprianou.ProofPreparation.poisson_prm_eval_real_second_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:24:28.535713+00:00
-- url     : https://prove2.me/theorems/9023ca2f-6b54-41ff-bdbd-414f39f0a3f8
-- title:
--   Exact real second moment of a finite-intensity Poisson region count
-- statement:
--   The real Bochner integral of the squared Poisson random-measure count on a finite-intensity measurable region equals the squared intensity plus the intensity. Direct consequence of the Proved indicator stochastic-integral second moment and an explicit, typed samplewise indicator/count equality. A reusable diagonal term for Chapter 2 Theorem 2.7 and its finite simple-function extensions.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.7, finite-region Poisson second moment.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_indicator_integral_second_moment
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_eval_real_second_moment
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A : Set E) (hA : MeasurableSet A) (hfin : m A < ⊤) :
    (∫ ω, ((ProbabilityTheory.poissonRandomMeasure K Y ω A).toReal) ^ 2 ∂P) =
      (m A).toReal ^ 2 + (m A).toReal := by sorry
end Kyprianou.ProofPreparation
