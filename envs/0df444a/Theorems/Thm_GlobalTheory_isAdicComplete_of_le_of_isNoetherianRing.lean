-- Prove2me | Theorems.Thm_GlobalTheory_isAdicComplete_of_le_of_isNoetherianRing
-- name    : GlobalTheory.isAdicComplete_of_le_of_isNoetherianRing
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:55:53.97449+00:00
-- url     : https://prove2.me/theorems/1c279d37-9619-47a0-b8f5-eb2a10583b7d
-- title:
--   Global Theory: is Adic Complete of le of is Noetherian Ring
-- statement:
--   The Global Theory construction uses the is Adic Complete of le of is Noetherian Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAdicCompleteOfLeOfIsNoetherianRing.lean#L5-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAdicCompleteOfLeOfIsNoetherianRing.lean#L5-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAdicCompleteOfLeOfIsNoetherianRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.isAdicComplete_of_le_of_isNoetherianRing (R : Type) [CommRing R] [IsNoetherianRing R]
    (I J : Ideal R) (hIJ : I ≤ J) (hJ : IsAdicComplete J R) : IsAdicComplete I R := by sorry
