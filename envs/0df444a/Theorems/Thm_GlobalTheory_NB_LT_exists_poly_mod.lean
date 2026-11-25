-- Prove2me | Theorems.Thm_GlobalTheory_NB_LT_exists_poly_mod
-- name    : GlobalTheory.NB.LT.exists_poly_mod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:30.785426+00:00
-- url     : https://prove2.me/theorems/0840f197-f89c-4cec-b3c4-329914174b29
-- title:
--   LT: exists poly mod
-- statement:
--   The LT construction uses the exists poly mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdSubOfDvdSubX.lean#L44-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdSubOfDvdSubX.lean#L44-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdSubOfDvdSubX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.NB GlobalTheory.NB.LT
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ}
open PowerSeries
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ}

theorem GlobalTheory.NB.LT.exists_poly_mod [Nontrivial R] {I : Ideal R} [IsAdicComplete I R] {p : Polynomial R}
    (H : p.IsDistinguishedAt I) (a : R⟦X⟧) :
    ∃ r : Polynomial R, r.degree < p.degree ∧ (p : R⟦X⟧) ∣ a - r := by sorry
