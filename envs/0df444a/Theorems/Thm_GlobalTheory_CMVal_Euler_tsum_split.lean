-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_tsum_split
-- name    : GlobalTheory.CMVal.Euler.tsum_split
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:18:51.836432+00:00
-- url     : https://prove2.me/theorems/b9717207-0721-48ce-8d56-cff144906c5e
-- title:
--   Euler: tsum split
-- statement:
--   The Euler construction uses the tsum split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L44-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L44-L54

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

theorem GlobalTheory.CMVal.Euler.tsum_split (hω : ∀ u ∈ U, ω u = 1) {B M M₁ M' : Set G} (hB : Summable (cs U ω B)) (h : M ⊆ B) (h₁ : M₁ ⊆ M)
    (hM' : Stable U M') (π : G) (hπ : ∀ y, π⁻¹ * y ∈ M' ↔ y ∈ M ∧ y ∉ M₁) :
    ∑' z, cs U ω M z = ∑' z, cs U ω M₁ z + ω π * ∑' z, cs U ω M' z := by sorry
