-- Prove2me | Theorems.Thm_GlobalTheory_GaussMarginal_gaussProb_eq_complexGaussian
-- name    : GlobalTheory.GaussMarginal.gaussProb_eq_complexGaussian
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:55:39.098425+00:00
-- url     : https://prove2.me/theorems/aa3236bc-1533-4ce1-82ee-562654e87c9b
-- title:
--   Gauss Marginal: gauss Prob eq complex Gaussian
-- statement:
--   The Gauss Marginal construction uses the gauss Prob eq complex Gaussian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianFirstCoordsMeasurePreserving.lean#L58-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianFirstCoordsMeasurePreserving.lean#L58-L75

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

theorem GlobalTheory.GaussMarginal.gaussProb_eq_complexGaussian (k : ℕ) :
    gaussProb k = GlobalTheory.complexGaussian (EuclideanSpace ℂ (Fin k)) k := by sorry
