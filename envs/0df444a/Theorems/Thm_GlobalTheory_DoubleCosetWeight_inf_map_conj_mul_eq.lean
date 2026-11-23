-- Prove2me | Theorems.Thm_GlobalTheory_DoubleCosetWeight_inf_map_conj_mul_eq
-- name    : GlobalTheory.DoubleCosetWeight.inf_map_conj_mul_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:21.623803+00:00
-- url     : https://prove2.me/theorems/6080541a-4750-46f8-94dd-c3686121397c
-- title:
--   Double Coset Weight: inf map conj mul eq
-- statement:
--   The Double Coset Weight construction uses the inf map conj mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetRelIndexInfConjConst.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetRelIndexInfConjConst.lean#L7-L21

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

theorem GlobalTheory.DoubleCosetWeight.inf_map_conj_mul_eq {G : Type} [Group G] (T K : Subgroup G) {t k : G}
    (ht : t ∈ T) (hk : k ∈ K) (q : G) :
    T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom =
      (T ⊓ K.map (MulAut.conj q).toMonoidHom).map (MulAut.conj t).toMonoidHom := by sorry
