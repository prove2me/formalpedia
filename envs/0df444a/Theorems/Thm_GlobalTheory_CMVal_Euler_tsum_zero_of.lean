-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_tsum_zero_of
-- name    : GlobalTheory.CMVal.Euler.tsum_zero_of
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:22:00.537797+00:00
-- url     : https://prove2.me/theorems/66329767-acd2-4622-bcb6-f9f56b7e43bc
-- title:
--   Euler: tsum zero of
-- statement:
--   The Euler construction uses the tsum zero of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L56-L62

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {G : Type} [CommGroup G] (U : Subgroup G) (ω : G →* ℂ)
variable {U ω}

theorem GlobalTheory.CMVal.Euler.tsum_zero_of (hω : ∀ u ∈ U, ω u = 1) {M : Set G} (hM : Stable U M) (u : G) (hu : ω u ≠ 1)
    (h : ∀ y, u⁻¹ * y ∈ M ↔ y ∈ M) : ∑' z, cs U ω M z = 0 := by sorry
