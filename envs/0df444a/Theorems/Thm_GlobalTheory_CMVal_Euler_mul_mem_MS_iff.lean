-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_mul_mem_MS_iff
-- name    : GlobalTheory.CMVal.Euler.mul_mem_MS_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:20:00.424698+00:00
-- url     : https://prove2.me/theorems/53006842-317a-4465-909d-8ffef2c69c8c
-- title:
--   Euler: mul mem MS iff
-- statement:
--   The Euler construction uses the mul mem MS iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L187-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L187-L192

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

theorem GlobalTheory.CMVal.Euler.mul_mem_MS_iff {m : HeightOneSpectrum (OF E) → ℕ} {T : Finset (HeightOneSpectrum (𝓞 E))} {u : (Af E)ˣ}
    (hu : ∀ v, LocIn (m v) v (u : Af E)) (hu' : ∀ w, Valued.v ((u : Af E) w) = 1) (y : (Af E)ˣ) :
    y * u ∈ MS m T ↔ y ∈ MS m T := by sorry
