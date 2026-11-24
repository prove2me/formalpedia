-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_stable_MS
-- name    : GlobalTheory.CMVal.Euler.stable_MS
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:19:26.738706+00:00
-- url     : https://prove2.me/theorems/617afcad-085f-44ae-8c70-2e81085ab517
-- title:
--   Euler: stable MS
-- statement:
--   The Euler construction uses the stable MS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L194-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L194-L196

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

theorem GlobalTheory.CMVal.Euler.stable_MS {c : Ideal (OF E)} {m : HeightOneSpectrum (OF E) → ℕ} (hm : ∀ v, m v ≤ expIn c v)
    (T : Finset (HeightOneSpectrum (𝓞 E))) : Stable (hatOUnits c) (MS m T) := by sorry
