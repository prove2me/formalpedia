-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_omega_apply
-- name    : GlobalTheory.CMVal.Euler.omega_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:19:24.40819+00:00
-- url     : https://prove2.me/theorems/41c1a71a-0c4d-483c-99aa-fd35dee00564
-- title:
--   Euler: omega apply
-- statement:
--   The Euler construction uses the omega apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L142-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L142-L142

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

theorem GlobalTheory.CMVal.Euler.omega_apply (χ : HChar E) (S : ℂ) (y : (Af E)ˣ) : omega χ S y = (finPart χ y : ℂ) * ((modF y : ℝ) : ℂ) ^ S := by sorry
