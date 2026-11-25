-- Prove2me | Theorems.Thm_GlobalTheory_SphereMeanDrop_radProb_log_mean
-- name    : GlobalTheory.SphereMeanDrop.radProb_log_mean
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:20:14.072134+00:00
-- url     : https://prove2.me/theorems/cc0a5377-4961-4de1-a3d8-3d4d658e4dc3
-- title:
--   Sphere Mean Drop: rad Prob log mean
-- statement:
--   The Sphere Mean Drop construction uses the rad Prob log mean property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianRadialLawProbabilityLogIntegrableMean.lean#L10-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianRadialLawProbabilityLogIntegrableMean.lean#L10-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianRadialLawProbabilityLogIntegrableMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop
open GlobalTheory GlobalTheory.SphereMeanDrop

theorem GlobalTheory.SphereMeanDrop.radProb_log_mean : ∀ (n : ℕ), 0 < n → IsProbabilityMeasure (radProb n) ∧
    Integrable (fun r : Ioi (0:ℝ) => Real.log r) (radProb n) ∧
    ∫ r, Real.log (r : ℝ) ∂(radProb n) = radK (2 * n - 1) / radJ (2 * n - 1) := by sorry
