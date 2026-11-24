-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_tsum_fin
-- name    : GlobalTheory.CMVal.Euler.tsum_fin
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:19:58.013263+00:00
-- url     : https://prove2.me/theorems/6a978124-fda8-442e-a9de-fdcab5a57de5
-- title:
--   Euler: tsum fin
-- statement:
--   The Euler construction uses the tsum fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L64-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L64-L83

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

theorem GlobalTheory.CMVal.Euler.tsum_fin (hω : ∀ u ∈ U, ω u = 1) {B M M' : Set G} (hB : Summable (cs U ω B)) (h : M' ⊆ B) (hM : Stable U M)
    {ι : Type} (R : Finset ι) (g : ι → G) (hg : ∀ r ∈ R, ω (g r) = 1)
    (h1 : ∀ y ∈ M', ∃! r, r ∈ R ∧ (g r)⁻¹ * y ∈ M) (h2 : ∀ r ∈ R, ∀ y, (g r)⁻¹ * y ∈ M → y ∈ M') :
    ∑' z, cs U ω M' z = R.card * ∑' z, cs U ω M z := by sorry
