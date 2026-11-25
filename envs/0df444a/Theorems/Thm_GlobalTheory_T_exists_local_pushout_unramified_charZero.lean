-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_local_pushout_unramified_charZero
-- name    : GlobalTheory.T.exists_local_pushout_unramified_charZero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:30:19.826573+00:00
-- url     : https://prove2.me/theorems/3ce10cd4-e233-5c53-89f9-9853effa6aae
-- title:
--   T: exists local pushout unramified char Zero
-- statement:
--   The T construction uses the exists local pushout unramified char Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLocalPushoutUnramifiedCharZeroStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLocalPushoutUnramifiedCharZeroStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalPushoutUnramifiedCharZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalPushoutUnramifiedCharZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_local_pushout_unramified_charZero : ∀ (A V V' : Type) [CommRing A] [CommRing V] [IsLocalRing V] [CommRing V'] [IsLocalRing V'] (f : A →+* V) (f' : A →+* V'), f'.Flat → (maximalIdeal V).comap f = (maximalIdeal V').comap f' → ((maximalIdeal V).comap f).map f = maximalIdeal V → ((maximalIdeal V').comap f').map f' = maximalIdeal V' → CharZero (ResidueField V) → ∃ (B : Type) (_ : CommRing B) (_ : IsLocalRing B) (g : V →+* B) (g' : V' →+* B), g.comp f = g'.comp f' ∧ g.Flat ∧ (maximalIdeal V).map g = maximalIdeal B ∧ (maximalIdeal V').map g' = maximalIdeal B := by sorry
