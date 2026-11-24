-- Prove2me | Theorems.Thm_GlobalTheory_CompleteDiscreteValuationRing_exists_complete_dvr
-- name    : GlobalTheory.CompleteDiscreteValuationRing.exists_complete_dvr
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:24:36.528614+00:00
-- url     : https://prove2.me/theorems/f8e704a9-3643-48de-822b-d80778c2c815
-- title:
--   Complete Discrete Valuation Ring: exists complete dvr
-- statement:
--   The Complete Discrete Valuation Ring construction uses the exists complete dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDvrOfDimOne.lean#L223-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDvrOfDimOne.lean#L223-L245

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDvrOfDimOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CompleteDiscreteValuationRing

theorem GlobalTheory.CompleteDiscreteValuationRing.exists_complete_dvr (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (t : A) (ht0 : t ≠ 0) (ht : ¬ IsUnit t) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (f : A →+* W), IsAdicComplete (maximalIdeal W) W ∧ Function.Injective f ∧
        ¬ IsUnit (f t) := by sorry
