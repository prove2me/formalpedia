-- Prove2me | Theorems.Thm_GlobalTheory_exists_highest_vector
-- name    : GlobalTheory.exists_highest_vector
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:37:59.776832+00:00
-- url     : https://prove2.me/theorems/b7e274f9-6da4-422a-9c60-655170cee5ef
-- title:
--   Global Theory: exists highest vector
-- statement:
--   The Global Theory construction uses the exists highest vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsJointIntEigenvectorOfStable.lean#L72-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsJointIntEigenvectorOfStable.lean#L72-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsJointIntEigenvectorOfStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_highest_vector {K V T : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] [Fintype T] [DecidableEq T] {m : ℕ}
    (e : T → Fin m → Fin m → Module.End K V)
    (he : ∀ t t' i k l, e t i i * e t' k l - e t' k l * e t i i = (if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0) : K) else 0) • e t' k l)
    (hdiag : ⨆ κ : T → Fin m → ℤ, (⨅ t, ⨅ i, Module.End.eigenspace (e t i i) (κ t i : K)) = ⊤)
    (W : Submodule K V) [FiniteDimensional K W] (hW : ∀ t i j, ∀ w ∈ W, e t i j w ∈ W) (hW0 : W ≠ ⊥) :
    ∃ v ∈ W, v ≠ 0 ∧ (∀ t i j, i < j → e t i j v = 0) ∧ ∃ κ : T → Fin m → ℤ, ∀ t i, e t i i v = (κ t i : K) • v := by sorry
