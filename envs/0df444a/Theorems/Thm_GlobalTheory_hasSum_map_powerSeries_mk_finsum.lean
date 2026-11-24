-- Prove2me | Theorems.Thm_GlobalTheory_hasSum_map_powerSeries_mk_finsum
-- name    : GlobalTheory.hasSum_map_powerSeries_mk_finsum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:54:20.802799+00:00
-- url     : https://prove2.me/theorems/d479d681-9e4f-4992-b037-b647a6f0b4a5
-- title:
--   Global Theory: has Sum map power Series mk finsum
-- statement:
--   The Global Theory construction uses the has Sum map power Series mk finsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HasSumMapPowerSeriesMkFinsum.lean#L6-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HasSumMapPowerSeriesMkFinsum.lean#L6-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HasSumMapPowerSeriesMkFinsum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory

theorem GlobalTheory.hasSum_map_powerSeries_mk_finsum : ∀ (O K Z : Type) [CommRing O] [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (φ : PowerSeries O →+* K), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (deg : Z → ℕ), (∀ n, {z | deg z = n}.Finite) → ∀ a : Z → O, HasSum (fun z => φ (PowerSeries.C (a z)) * φ PowerSeries.X ^ deg z) (φ (PowerSeries.mk fun n => ∑ᶠ (z : Z) (_ : deg z = n), a z)) := by sorry
