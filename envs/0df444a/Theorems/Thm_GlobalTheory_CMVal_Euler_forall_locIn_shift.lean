-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_forall_locIn_shift
-- name    : GlobalTheory.CMVal.Euler.forall_locIn_shift
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:19:49.457017+00:00
-- url     : https://prove2.me/theorems/d1735465-10b4-4703-811d-d6171839eaa8
-- title:
--   Euler: forall loc In shift
-- statement:
--   The Euler construction uses the forall loc In shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L205-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L205-L215

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

theorem GlobalTheory.CMVal.Euler.forall_locIn_shift {m m' : HeightOneSpectrum (OF E) → ℕ} {v : HeightOneSpectrum (OF E)} (hm : ∀ v' ≠ v, m' v' = m v')
    {π : (Af E)ˣ} (hπ : ∀ w, ¬ Over w v → (π : Af E) w = 1) (y : (Af E)ˣ) :
    (∀ v', LocIn (m' v') v' ((π⁻¹ * y : (Af E)ˣ) : Af E)) ↔
      LocIn (m' v) v ((π⁻¹ * y : (Af E)ˣ) : Af E) ∧ ∀ v' ≠ v, LocIn (m v') v' (y : Af E) := by sorry
