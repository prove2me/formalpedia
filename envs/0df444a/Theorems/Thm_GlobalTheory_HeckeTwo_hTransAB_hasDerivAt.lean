-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_hTransAB_hasDerivAt
-- name    : GlobalTheory.HeckeTwo.hTransAB_hasDerivAt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:12:58.908625+00:00
-- url     : https://prove2.me/theorems/e38c0a75-80a6-4b19-ad6d-25ca6211f5d7
-- title:
--   Hecke Two: h Trans AB has Deriv At
-- statement:
--   The Hecke Two construction uses the h Trans AB has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeHankelTransformABHasDerivAtY.lean#L181-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeHankelTransformABHasDerivAtY.lean#L181-L227

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABHasDerivAtY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo
open MeasureTheory GlobalTheory.HeckeTwoDY

theorem GlobalTheory.HeckeTwo.hTransAB_hasDerivAt : ∀ (a b : ℕ) (σ : ℂ) (ν y : ℝ), 2 ≤ a + b → σ ∈ halfPlane → y ≠ 0 →
    HasDerivAt (fun y' : ℝ => hTransAB a b σ ν y')
      (I * (-(a : ℂ) - σ) * hTransAB (a + 1) b σ ν y + I * ((b : ℂ) + σ) * hTransAB a (b + 1) σ ν y) y := by sorry
