-- Prove2me | Theorems.Thm_GlobalTheory_RelIndexOfMap_relIndex_eq_of_map
-- name    : GlobalTheory.RelIndexOfMap.relIndex_eq_of_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:42.653559+00:00
-- url     : https://prove2.me/theorems/f0739f9c-e644-4859-a1e2-226a223c0b65
-- title:
--   Rel Index Of Map: rel Index eq of map
-- statement:
--   The Rel Index Of Map construction uses the rel Index eq of map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RelIndexEqOfMap.lean#L5-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RelIndexEqOfMap.lean#L5-L13

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

theorem GlobalTheory.RelIndexOfMap.relIndex_eq_of_map {X P : Type} [Group X] [Group P] (φ : X →* P) (A B : Subgroup X)
    (U V : Subgroup P) (hA : A.map φ = U) (hB : ∀ a ∈ A, a ∈ B ↔ φ a ∈ V) :
    B.relIndex A = V.relIndex U := by sorry
