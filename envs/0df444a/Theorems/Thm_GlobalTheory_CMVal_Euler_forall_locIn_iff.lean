-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_forall_locIn_iff
-- name    : GlobalTheory.CMVal.Euler.forall_locIn_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:18:58.963518+00:00
-- url     : https://prove2.me/theorems/919168b9-4436-4601-adc0-e8579baa87d2
-- title:
--   Euler: forall loc In iff
-- statement:
--   The Euler construction uses the forall loc In iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L217-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L217-L222

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

theorem GlobalTheory.CMVal.Euler.forall_locIn_iff (m : HeightOneSpectrum (OF E) → ℕ) (v : HeightOneSpectrum (OF E)) (y : Af E) :
    (∀ v', LocIn (m v') v' y) ↔ LocIn (m v) v y ∧ ∀ v' ≠ v, LocIn (m v') v' y := by sorry
