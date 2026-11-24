-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_omega_unit
-- name    : GlobalTheory.CMVal.Euler.omega_unit
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:19:28.836807+00:00
-- url     : https://prove2.me/theorems/4742ba24-a597-49f0-8229-5993a9c12efb
-- title:
--   Euler: omega unit
-- statement:
--   The Euler construction uses the omega unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L144-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L144-L146

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

theorem GlobalTheory.CMVal.Euler.omega_unit (χ : HChar E) (S : ℂ) {y : (Af E)ˣ} (h : ∀ w, Valued.v ((y : Af E) w) = 1) :
    omega χ S y = finPart χ y := by sorry
