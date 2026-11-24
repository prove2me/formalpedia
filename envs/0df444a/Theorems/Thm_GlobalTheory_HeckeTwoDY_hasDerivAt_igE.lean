-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwoDY_hasDerivAt_igE
-- name    : GlobalTheory.HeckeTwoDY.hasDerivAt_igE
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:14:26.855464+00:00
-- url     : https://prove2.me/theorems/b843efaa-3f4d-4721-b1a5-70f5c4a9d400
-- title:
--   Hecke Two DY: has Deriv At ig E
-- statement:
--   The Hecke Two DY construction uses the has Deriv At ig E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeHankelTransformABHasDerivAtY.lean#L106-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeHankelTransformABHasDerivAtY.lean#L106-L119

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
open GlobalTheory GlobalTheory.HeckeTwoDY
open MeasureTheory

theorem GlobalTheory.HeckeTwoDY.hasDerivAt_igE (a b : ℕ) (σ : ℂ) (ν t : ℝ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun y' => igE a b σ ν y' t)
      (I * (-(a : ℂ) - σ) * igE (a + 1) b σ ν y t + I * ((b : ℂ) + σ) * igE a (b + 1) σ ν y t) y := by sorry
