-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_tsum_translate
-- name    : GlobalTheory.CMVal.Euler.tsum_translate
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:19:21.17347+00:00
-- url     : https://prove2.me/theorems/83160b4e-b1a5-4736-abf4-f39b15f2337c
-- title:
--   Euler: tsum translate
-- statement:
--   The Euler construction uses the tsum translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L28-L38

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

theorem GlobalTheory.CMVal.Euler.tsum_translate (hω : ∀ u ∈ U, ω u = 1) {M : Set G} (hM : Stable U M) (π : G) :
    ∑' z, cs U ω {y | π⁻¹ * y ∈ M} z = ω π * ∑' z, cs U ω M z := by sorry
