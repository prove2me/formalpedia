-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_lintegral_sq
-- name    : Kyprianou.ProofPreparation.poisson_prm_eval_lintegral_sq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:01:48.582136+00:00
-- url     : https://prove2.me/theorems/d6a3d634-4c94-4061-bb93-7296702aced1
-- title:
--   Squared Poisson random-measure count on a finite-intensity measurable set
-- statement:
--   The squared real-valued Poisson random-measure count on any finite-intensity measurable region has ENNReal mean λ²+λ; this transfers the Proved Poisson count second-moment identity through the exact point-family evaluation law. Sublemma towards Chapter 2 Theorem 2.7 second moment.
-- source:
--   Kyprianou (2006) Chapter 2 Theorem 2.7 pp. 41–43; finite-region count moment.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_map_poissonRandomMeasure_apply
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_lintegral_sq_nat_count
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_eval_lintegral_sq
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A : Set E) (hA : MeasurableSet A) (hfin : m A < ⊤) :
    (∫⁻ ω, ENNReal.ofReal
      (((ProbabilityTheory.poissonRandomMeasure K Y ω A).toReal) ^ 2) ∂P) =
      ENNReal.ofReal ((m A).toReal ^ 2 + (m A).toReal) := by sorry
end Kyprianou.ProofPreparation
