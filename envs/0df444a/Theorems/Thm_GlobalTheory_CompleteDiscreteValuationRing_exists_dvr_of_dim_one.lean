-- Prove2me | Theorems.Thm_GlobalTheory_CompleteDiscreteValuationRing_exists_dvr_of_dim_one
-- name    : GlobalTheory.CompleteDiscreteValuationRing.exists_dvr_of_dim_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:24:29.686891+00:00
-- url     : https://prove2.me/theorems/6dce5d77-f03b-4aa3-90c2-fcb179dbbd6d
-- title:
--   Complete Discrete Valuation Ring: exists dvr of dim one
-- statement:
--   The Complete Discrete Valuation Ring construction uses the exists dvr of dim one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDvrOfDimOne.lean#L82-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDvrOfDimOne.lean#L82-L149

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

theorem GlobalTheory.CompleteDiscreteValuationRing.exists_dvr_of_dim_one (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O]
    [IsNoetherianRing O] [Ring.KrullDimLE 1 O] (t : O) (ht0 : t ≠ 0) (ht : ¬ IsUnit t) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (f : O →+* W), Function.Injective f ∧ ¬ IsUnit (f t) := by sorry
