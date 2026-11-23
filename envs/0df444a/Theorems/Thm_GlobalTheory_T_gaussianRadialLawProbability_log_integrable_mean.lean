-- Prove2me | Theorems.Thm_GlobalTheory_T_gaussianRadialLawProbability_log_integrable_mean
-- name    : GlobalTheory.T.gaussianRadialLawProbability_log_integrable_mean
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:12.122284+00:00
-- url     : https://prove2.me/theorems/db1a1ed6-091b-410c-9b85-b5bb72205ad0
-- title:
--   T: gaussian Radial Law Probability log integrable mean
-- statement:
--   The T construction uses the gaussian Radial Law Probability log integrable mean property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianRadialLawProbabilityLogIntegrableMeanStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianRadialLawProbabilityLogIntegrableMeanStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianRadialLawProbabilityLogIntegrableMean
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianRadialLawProbabilityLogIntegrableMeanStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.gaussianRadialLawProbability_log_integrable_mean : ∀ (n : ℕ), 0 < n → IsProbabilityMeasure (radProb n) ∧ Integrable (fun r : Ioi (0:ℝ) => Real.log r) (radProb n) ∧ ∫ r, Real.log (r : ℝ) ∂(radProb n) = radK (2 * n - 1) / radJ (2 * n - 1) := by sorry
