-- Prove2me | Theorems.Thm_GlobalTheory_UnramPushout_exists_local_pushout
-- name    : GlobalTheory.UnramPushout.exists_local_pushout
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:47:06.631817+00:00
-- url     : https://prove2.me/theorems/78869264-6a0a-4108-b840-81c084f0fc87
-- title:
--   Unram Pushout: exists local pushout
-- statement:
--   The Unram Pushout construction uses the exists local pushout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLocalPushoutUnramifiedCharZero.lean#L50-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLocalPushoutUnramifiedCharZero.lean#L50-L135

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalPushoutUnramifiedCharZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.UnramPushout
open TensorProduct

theorem GlobalTheory.UnramPushout.exists_local_pushout (A V V' : Type) [CommRing A] [CommRing V] [IsLocalRing V]
    [CommRing V'] [IsLocalRing V'] (f : A →+* V) (f' : A →+* V') (hf' : f'.Flat)
    (hP : (maximalIdeal V).comap f = (maximalIdeal V').comap f')
    (hV : ((maximalIdeal V).comap f).map f = maximalIdeal V)
    (hV' : ((maximalIdeal V').comap f').map f' = maximalIdeal V')
    (h0 : CharZero (ResidueField V)) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsLocalRing B) (g : V →+* B) (g' : V' →+* B),
      g.comp f = g'.comp f' ∧ g.Flat ∧ (maximalIdeal V).map g = maximalIdeal B ∧
        (maximalIdeal V').map g' = maximalIdeal B := by sorry
