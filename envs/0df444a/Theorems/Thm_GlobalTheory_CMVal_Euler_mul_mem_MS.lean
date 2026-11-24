-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_mul_mem_MS
-- name    : GlobalTheory.CMVal.Euler.mul_mem_MS
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:19:43.363165+00:00
-- url     : https://prove2.me/theorems/96545e19-6125-47d7-a2c6-fa705305d568
-- title:
--   Euler: mul mem MS
-- statement:
--   The Euler construction uses the mul mem MS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L180-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L180-L182

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

theorem GlobalTheory.CMVal.Euler.mul_mem_MS {m : HeightOneSpectrum (OF E) → ℕ} {T : Finset (HeightOneSpectrum (𝓞 E))} {u y : (Af E)ˣ}
    (hu : ∀ v, LocIn (m v) v (u : Af E)) (hu' : ∀ w, Valued.v ((u : Af E) w) = 1) (hy : y ∈ MS m T) : y * u ∈ MS m T := by sorry
