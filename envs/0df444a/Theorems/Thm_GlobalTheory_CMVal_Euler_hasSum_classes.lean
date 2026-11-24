-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_hasSum_classes
-- name    : GlobalTheory.CMVal.Euler.hasSum_classes
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:19:03.328196+00:00
-- url     : https://prove2.me/theorems/a29b3cd0-349b-4f47-a164-6149f369cdd1
-- title:
--   Euler: has Sum classes
-- statement:
--   The Euler construction uses the has Sum classes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L103-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L103-L117

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

theorem GlobalTheory.CMVal.Euler.hasSum_classes {M : Set G} (hM : Stable U M) (hs : Summable (cs U ω M)) :
    HasSum (fun z : {z : G ⧸ U // ∃ y : G, (QuotientGroup.mk y : G ⧸ U) = z ∧ y ∈ M} => ω z.1.out) (∑' z, cs U ω M z) := by sorry
