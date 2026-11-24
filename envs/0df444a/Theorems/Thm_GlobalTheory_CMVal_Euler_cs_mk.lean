-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_cs_mk
-- name    : GlobalTheory.CMVal.Euler.cs_mk
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:19:54.22874+00:00
-- url     : https://prove2.me/theorems/d3d3faf6-0746-46b8-a968-bb80282d29f6
-- title:
--   Euler: cs mk
-- statement:
--   The Euler construction uses the cs mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L20-L26

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

theorem GlobalTheory.CMVal.Euler.cs_mk (hω : ∀ u ∈ U, ω u = 1) {M : Set G} (hM : Stable U M) (y : G) :
    cs U ω M (QuotientGroup.mk y) = M.indicator ω y := by sorry
