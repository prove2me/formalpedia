-- Prove2me | Theorems.Thm_GlobalTheory_NB_LT_poly_dvd_of_dvd
-- name    : GlobalTheory.NB.LT.poly_dvd_of_dvd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:30:22.169225+00:00
-- url     : https://prove2.me/theorems/38f51383-194e-48db-b47b-035de8227f96
-- title:
--   LT: poly dvd of dvd
-- statement:
--   The LT construction uses the poly dvd of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdSubOfDvdSubX.lean#L61-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdSubOfDvdSubX.lean#L61-L85

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

theorem GlobalTheory.NB.LT.poly_dvd_of_dvd {I : Ideal R} [IsAdicComplete I R] {p : Polynomial R}
    (H : p.IsDistinguishedAt I) {r : Polynomial R} (h : (p : R⟦X⟧) ∣ (r : R⟦X⟧)) : p ∣ r := by sorry
