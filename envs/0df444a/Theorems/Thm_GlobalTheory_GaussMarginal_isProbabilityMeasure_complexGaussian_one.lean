-- Prove2me | Theorems.Thm_GlobalTheory_GaussMarginal_isProbabilityMeasure_complexGaussian_one
-- name    : GlobalTheory.GaussMarginal.isProbabilityMeasure_complexGaussian_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:21.096412+00:00
-- url     : https://prove2.me/theorems/4532f3db-30df-4d80-8b7b-8fb9da17c42f
-- title:
--   Gauss Marginal: is Probability Measure complex Gaussian one
-- statement:
--   The Gauss Marginal construction uses the is Probability Measure complex Gaussian one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianFirstCoordsMeasurePreserving.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianFirstCoordsMeasurePreserving.lean#L54-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianFirstCoordsMeasurePreserving
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop
noncomputable section
open GlobalTheory GlobalTheory.GaussMarginal
open Real

theorem GlobalTheory.GaussMarginal.isProbabilityMeasure_complexGaussian_one :
    IsProbabilityMeasure (GlobalTheory.complexGaussian ℂ 1) := by sorry
