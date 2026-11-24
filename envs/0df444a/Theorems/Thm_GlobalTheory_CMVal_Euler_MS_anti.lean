-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_MS_anti
-- name    : GlobalTheory.CMVal.Euler.MS_anti
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:19:51.568652+00:00
-- url     : https://prove2.me/theorems/9b61f59b-9a97-42bd-98d2-c97817ad5644
-- title:
--   Euler: MS anti
-- statement:
--   The Euler construction uses the MS anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L177-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L177-L178

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

theorem GlobalTheory.CMVal.Euler.MS_anti (m : HeightOneSpectrum (OF E) → ℕ) {T T' : Finset (HeightOneSpectrum (𝓞 E))} (h : T ⊆ T') : MS m T' ⊆ MS m T := by sorry
