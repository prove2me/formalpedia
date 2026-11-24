-- Prove2me | Theorems.Thm_GlobalTheory_SaturatedNotDvd_exists_not_dvd
-- name    : GlobalTheory.SaturatedNotDvd.exists_not_dvd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:48:23.331939+00:00
-- url     : https://prove2.me/theorems/1e5d31a1-23e4-47de-9ff0-2b89e1650392
-- title:
--   Saturated Not Dvd: exists not dvd
-- statement:
--   The Saturated Not Dvd construction uses the exists not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSaturated.lean#L45-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSaturated.lean#L45-L56

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

theorem GlobalTheory.SaturatedNotDvd.exists_not_dvd {A : Type u_1} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] {x : A}
    (hx : ¬ IsUnit x) {K : Ideal A} (hK : K ≠ ⊥) (hs : ∀ u, x * u ∈ K → u ∈ K) :
    ∃ u ∈ K, ¬ x ∣ u := by sorry
