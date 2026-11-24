-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_omega_unifAt
-- name    : GlobalTheory.CMVal.Euler.omega_unifAt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:18:50.952847+00:00
-- url     : https://prove2.me/theorems/5d153617-4eb4-4b16-ad8a-1c6c544d9108
-- title:
--   Euler: omega unif At
-- statement:
--   The Euler construction uses the omega unif At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L157-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L157-L159

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

theorem GlobalTheory.CMVal.Euler.omega_unifAt (χ : HChar E) (S : ℂ) (w : HeightOneSpectrum (𝓞 E)) :
    omega χ S (unifAt w) = (val χ w : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-S) := by sorry
