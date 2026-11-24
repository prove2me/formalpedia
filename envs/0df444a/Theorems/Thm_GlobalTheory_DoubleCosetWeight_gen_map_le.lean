-- Prove2me | Theorems.Thm_GlobalTheory_DoubleCosetWeight_gen_map_le
-- name    : GlobalTheory.DoubleCosetWeight.gen_map_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:50:30.527453+00:00
-- url     : https://prove2.me/theorems/06cae0a7-accf-4ec7-a2b7-8ada845c191d
-- title:
--   Double Coset Weight: gen map le
-- statement:
--   The Double Coset Weight construction uses the gen map le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetRelIndexInfConjConst.lean#L26-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetRelIndexInfConjConst.lean#L26-L35

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

theorem GlobalTheory.DoubleCosetWeight.gen_map_le {G : Type} [Group G] (T K : Subgroup G) {t : G} (ht : t ∈ T) :
    (gen T K).map (MulAut.conj t).toMonoidHom ≤ gen T K := by sorry
