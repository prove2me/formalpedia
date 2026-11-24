-- Prove2me | Theorems.Thm_GlobalTheory_RelIndexOfMap_mem_map_conj
-- name    : GlobalTheory.RelIndexOfMap.mem_map_conj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:21:04.536285+00:00
-- url     : https://prove2.me/theorems/9391a8a4-18f4-402f-98ed-1ac053291c49
-- title:
--   Rel Index Of Map: mem map conj
-- statement:
--   The Rel Index Of Map construction uses the mem map conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RelIndexEqOfMap.lean#L56-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RelIndexEqOfMap.lean#L56-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RelIndexEqOfMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RelIndexOfMap

theorem GlobalTheory.RelIndexOfMap.mem_map_conj {H : Type} [Group H] (J : Subgroup H) (h x : H) :
    x ∈ Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : H → MulAut H) h)) J ↔
      h⁻¹ * x * h ∈ J := by sorry
