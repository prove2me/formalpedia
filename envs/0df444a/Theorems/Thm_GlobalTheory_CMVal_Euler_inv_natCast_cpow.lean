-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_inv_natCast_cpow
-- name    : GlobalTheory.CMVal.Euler.inv_natCast_cpow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:20:26.924814+00:00
-- url     : https://prove2.me/theorems/a9449850-734d-466a-9849-df74acbc0608
-- title:
--   Euler: inv nat Cast cpow
-- statement:
--   The Euler construction uses the inv nat Cast cpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L153-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L153-L155

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

theorem GlobalTheory.CMVal.Euler.inv_natCast_cpow (N : ℕ) (S : ℂ) : ((((N : ℝ)⁻¹ : ℝ)) : ℂ) ^ S = (N : ℂ) ^ (-S) := by sorry
