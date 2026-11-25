-- Prove2me | Theorems.Thm_GlobalTheory_highest_weight_antitone
-- name    : GlobalTheory.highest_weight_antitone
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:47:50.815905+00:00
-- url     : https://prove2.me/theorems/f5f53932-beff-5893-ae35-67cd2c2ff529
-- title:
--   Global Theory: highest weight antitone
-- statement:
--   The Global Theory construction uses the highest weight antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/Sl2NonnegWeightOfHighestWeightVector.lean#L129-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/Sl2NonnegWeightOfHighestWeightVector.lean#L129-L157

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_Sl2NonnegWeightOfHighestWeightVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.highest_weight_antitone {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {m : ℕ} (e : Fin m → Fin m → Module.End K V)
    (he : ∀ i j k l, e i j * e k l - e k l * e i j = (if j = k then e i l else 0) - (if l = i then e k j else 0))
    (W : Submodule K V) [FiniteDimensional K W] (hW : ∀ i j, ∀ w ∈ W, e i j w ∈ W)
    (v : V) (hvW : v ∈ W) (hv0 : v ≠ 0) (κ : Fin m → ℤ) (hv : ∀ i j, i < j → e i j v = 0) (hκ : ∀ i, e i i v = (κ i : K) • v) : Antitone κ := by sorry
