-- Prove2me | Theorems.Thm_GlobalTheory_DoubleCosetWeight_relIndex_eq
-- name    : GlobalTheory.DoubleCosetWeight.relIndex_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:50:17.630424+00:00
-- url     : https://prove2.me/theorems/bee042dc-ea20-4c5c-b6ae-19e5d07227f6
-- title:
--   Double Coset Weight: rel Index eq
-- statement:
--   The Double Coset Weight construction uses the rel Index eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetRelIndexInfConjConst.lean#L45-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetRelIndexInfConjConst.lean#L45-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetRelIndexInfConjConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DoubleCosetWeight
open Subgroup

theorem GlobalTheory.DoubleCosetWeight.relIndex_eq {G : Type} [Group G] (T C K : Subgroup G)
    (hC : ∀ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom ≤ C) :
    ∀ t ∈ T, ∀ k ∈ K, ∀ q : G,
      (T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom).relIndex C =
        (T ⊓ K.map (MulAut.conj q).toMonoidHom).relIndex C := by sorry
