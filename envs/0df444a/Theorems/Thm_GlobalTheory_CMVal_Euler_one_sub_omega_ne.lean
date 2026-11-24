-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_one_sub_omega_ne
-- name    : GlobalTheory.CMVal.Euler.one_sub_omega_ne
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:18:55.70282+00:00
-- url     : https://prove2.me/theorems/eb08afa5-8fd9-4c79-9655-edd0d5ef1d07
-- title:
--   Euler: one sub omega ne
-- statement:
--   The Euler construction uses the one sub omega ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L161-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L161-L167

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
open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.Euler.one_sub_omega_ne {χ : HChar E} (h : IsUnitary χ) {S : ℂ} (hS : 0 < S.re) (w : HeightOneSpectrum (𝓞 E)) :
    1 - omega χ S (unifAt w) ≠ 0 := by sorry
