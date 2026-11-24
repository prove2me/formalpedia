-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwoDY_hasDerivAt_invpow
-- name    : GlobalTheory.HeckeTwoDY.hasDerivAt_invpow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:14:38.10488+00:00
-- url     : https://prove2.me/theorems/86497c07-1e7a-4f99-a92a-5420d96837ac
-- title:
--   Hecke Two DY: has Deriv At invpow
-- statement:
--   The Hecke Two DY construction uses the has Deriv At invpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeHankelTransformABHasDerivAtY.lean#L82-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeHankelTransformABHasDerivAtY.lean#L82-L90

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

theorem GlobalTheory.HeckeTwoDY.hasDerivAt_invpow {f : ℝ → ℂ} {c : ℂ} {y : ℝ} (hf : HasDerivAt f c y) (hne : f y ≠ 0) (n : ℕ) :
    HasDerivAt (fun y' => (f y')⁻¹ ^ n) (-(n : ℂ) * c * (f y)⁻¹ ^ (n + 1)) y := by sorry
