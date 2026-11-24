-- Prove2me | Theorems.Thm_GlobalTheory_GaussMarginal_measurePreserving_firstCoords_gaussProb
-- name    : GlobalTheory.GaussMarginal.measurePreserving_firstCoords_gaussProb
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:54:24.837561+00:00
-- url     : https://prove2.me/theorems/2b117d48-3157-4275-a0bd-b676278c1b74
-- title:
--   Gauss Marginal: measure Preserving first Coords gauss Prob
-- statement:
--   The Gauss Marginal construction uses the measure Preserving first Coords gauss Prob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianFirstCoordsMeasurePreserving.lean#L122-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianFirstCoordsMeasurePreserving.lean#L122-L140

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

theorem GlobalTheory.GaussMarginal.measurePreserving_firstCoords_gaussProb :
    ∀ (N n : ℕ) (h : N ≤ n), MeasurePreserving (firstCoords h) (gaussProb n) (gaussProb N) := by sorry
