-- Prove2me | Theorems.Thm_GlobalTheory_adapted_coords_vanish_stmt
-- name    : GlobalTheory.adapted_coords_vanish_stmt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:52:48.024565+00:00
-- url     : https://prove2.me/theorems/b49581eb-acdd-54ff-9a89-6536d09d814d
-- title:
--   Global Theory: adapted coords vanish stmt
-- statement:
--   The Global Theory construction uses the adapted coords vanish stmt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LaurentSeriesAdaptedBasisCoordsVanishBeyondFinra.lean#L77-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LaurentSeriesAdaptedBasisCoordsVanishBeyondFinra.lean#L77-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LaurentSeriesAdaptedBasisCoordsVanishBeyondFinra
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

theorem GlobalTheory.adapted_coords_vanish_stmt : ∀ (F : Type) [Field F] (n : ℕ) (W : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ), (∀ j : Fin n, (j : ℕ) < Module.finrank (LaurentSeries F) W → (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) : LaurentSeries F)) ∈ W) → ∀ y : Fin n → PowerSeries F, (fun a => ((y a : PowerSeries F) : LaurentSeries F)) ∈ W → ∀ a : Fin n, Module.finrank (LaurentSeries F) W ≤ (a : ℕ) → (((g⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries F)).mulVec y) a = 0 := by sorry
