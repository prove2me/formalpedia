-- Prove2me | Theorems.Thm_GlobalTheory_exists_ringHom_powerSeries_root
-- name    : GlobalTheory.exists_ringHom_powerSeries_root
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:41:04.305127+00:00
-- url     : https://prove2.me/theorems/040c81b5-7334-42e4-8dbe-423920d797c5
-- title:
--   Global Theory: exists ring Hom power Series root
-- statement:
--   The Global Theory construction uses the exists ring Hom power Series root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsRingHomPowerSeriesRoot.lean#L121-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsRingHomPowerSeriesRoot.lean#L121-L133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRingHomPowerSeriesRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
open GlobalTheory

theorem GlobalTheory.exists_ringHom_powerSeries_root :
    ∀ (O K : Type) [CommRing O] [CommRing K] (φ : PowerSeries O →+* K) (k : ℕ) (t : K), 0 < k →
      t ^ k = φ PowerSeries.X → ∃ Φ : PowerSeries O →+* K,
        (∀ a, Φ (PowerSeries.C a) = φ (PowerSeries.C a)) ∧ Φ PowerSeries.X = t ∧
          ∀ f, Φ f ∈ Subring.closure (Set.range φ ∪ {t}) := by sorry
