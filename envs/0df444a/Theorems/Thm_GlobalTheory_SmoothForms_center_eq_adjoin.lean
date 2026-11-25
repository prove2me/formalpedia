-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_center_eq_adjoin
-- name    : GlobalTheory.SmoothForms.center_eq_adjoin
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:13:38.467182+00:00
-- url     : https://prove2.me/theorems/d23658f0-3673-4256-80ff-d79ae16ae07c
-- title:
--   Smooth Forms: center eq adjoin
-- statement:
--   The Smooth Forms construction uses the center eq adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PolarConjTranspose.lean#L134-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PolarConjTranspose.lean#L134-L145

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieSmoothAndLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieCommutatorEqBracketStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutatorGlGeneratorTensorWordMapMatrixUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemAdjoinGlActionOfCommuteTensorPermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BicommutantTensorFactorPermMemSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutantLiftModStableSelfAdjointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology
open Matrix
open GlobalTheory GlobalTheory.SmoothForms
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A}

theorem GlobalTheory.SmoothForms.center_eq_adjoin (hE : Formalism.REAL.GlRel E)
    (hgen : Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => E p.1 p.2) = ⊤) :
    Subalgebra.center ℂ A = Algebra.adjoin ℂ (Set.range (gelfA E)) := by sorry
