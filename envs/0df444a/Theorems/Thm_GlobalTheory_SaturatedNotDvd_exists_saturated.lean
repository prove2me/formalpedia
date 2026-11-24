-- Prove2me | Theorems.Thm_GlobalTheory_SaturatedNotDvd_exists_saturated
-- name    : GlobalTheory.SaturatedNotDvd.exists_saturated
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:48:34.793861+00:00
-- url     : https://prove2.me/theorems/e50c2e15-b77d-4350-9403-dbe086865581
-- title:
--   Saturated Not Dvd: exists saturated
-- statement:
--   The Saturated Not Dvd construction uses the exists saturated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSaturated.lean#L7-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSaturated.lean#L7-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSaturated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.SaturatedNotDvd

theorem GlobalTheory.SaturatedNotDvd.exists_saturated {A : Type u_1} [CommRing A] [IsDomain A] {x a b : A} (hx : Prime x)
    (hb : ¬ x ∣ b) {I : Ideal A} (hI : I ≠ ⊥) (h : ∀ r ∈ I, ∃ s ∈ I, a * r = b * s) :
    ∃ K : Ideal A, K ≠ ⊥ ∧ (∀ u, x * u ∈ K → u ∈ K) ∧ ∀ r ∈ K, ∃ s ∈ K, a * r = b * s := by sorry
