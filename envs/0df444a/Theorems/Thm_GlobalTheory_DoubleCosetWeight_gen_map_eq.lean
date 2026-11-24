-- Prove2me | Theorems.Thm_GlobalTheory_DoubleCosetWeight_gen_map_eq
-- name    : GlobalTheory.DoubleCosetWeight.gen_map_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:50:29.072713+00:00
-- url     : https://prove2.me/theorems/cf31781a-e2f2-4298-a1b5-95ec0d01060f
-- title:
--   Double Coset Weight: gen map eq
-- statement:
--   The Double Coset Weight construction uses the gen map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetRelIndexInfConjConst.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetRelIndexInfConjConst.lean#L37-L43

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

theorem GlobalTheory.DoubleCosetWeight.gen_map_eq {G : Type} [Group G] (T K : Subgroup G) {t : G} (ht : t ∈ T) :
    (gen T K).map (MulAut.conj t).toMonoidHom = gen T K := by sorry
