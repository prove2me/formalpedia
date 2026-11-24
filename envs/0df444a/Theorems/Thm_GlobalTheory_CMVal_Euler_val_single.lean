-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_val_single
-- name    : GlobalTheory.CMVal.Euler.val_single
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:19:37.11409+00:00
-- url     : https://prove2.me/theorems/5a65b97f-4ba1-4b35-bc89-22f519150d6a
-- title:
--   Euler: val single
-- statement:
--   The Euler construction uses the val single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L228-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L228-L232

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

theorem GlobalTheory.CMVal.Euler.val_single {P : HeightOneSpectrum (𝓞 E)} {x : (P.adicCompletion E)ˣ} (hx : Valued.v (x : P.adicCompletion E) = 1)
    (w : HeightOneSpectrum (𝓞 E)) : Valued.v ((single P x : Af E) w) = 1 := by sorry
