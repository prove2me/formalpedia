-- Prove2me | Theorems.Thm_GlobalTheory_CompleteDiscreteValuationRing_exists_complete
-- name    : GlobalTheory.CompleteDiscreteValuationRing.exists_complete
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:24:11.472853+00:00
-- url     : https://prove2.me/theorems/c3eaf133-e17b-487f-9920-9a711d892664
-- title:
--   Complete Discrete Valuation Ring: exists complete
-- statement:
--   The Complete Discrete Valuation Ring construction uses the exists complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDvrOfDimOne.lean#L196-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDvrOfDimOne.lean#L196-L221

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

theorem GlobalTheory.CompleteDiscreteValuationRing.exists_complete (B : Type) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (f : B →+* W), IsAdicComplete (maximalIdeal W) W ∧ Function.Injective f ∧ IsLocalHom f := by sorry
