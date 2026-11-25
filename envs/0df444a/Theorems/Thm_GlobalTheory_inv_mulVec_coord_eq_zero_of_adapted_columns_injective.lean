-- Prove2me | Theorems.Thm_GlobalTheory_inv_mulVec_coord_eq_zero_of_adapted_columns_injective
-- name    : GlobalTheory.inv_mulVec_coord_eq_zero_of_adapted_columns_injective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:56:10.784276+00:00
-- url     : https://prove2.me/theorems/c8d6618b-743a-40d1-b739-668e0e3dadd5
-- title:
--   Global Theory: inv mul Vec coord eq zero of adapted columns injective
-- statement:
--   The Global Theory construction uses the inv mul Vec coord eq zero of adapted columns injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LaurentSeriesAdaptedBasisCoordsVanishBeyondFinra.lean#L6-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LaurentSeriesAdaptedBasisCoordsVanishBeyondFinra.lean#L6-L65

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

theorem GlobalTheory.inv_mulVec_coord_eq_zero_of_adapted_columns_injective {R K : Type} [CommRing R] [Field K] (φ : R →+* K)
    (hφ : Function.Injective φ) (n : ℕ) (W : Submodule K (Fin n → K))
    (g : (Matrix (Fin n) (Fin n) R)ˣ)
    (hg : ∀ j : Fin n, (j : ℕ) < Module.finrank K W →
      (fun a => φ ((g : Matrix (Fin n) (Fin n) R) a j)) ∈ W)
    (y : Fin n → R) (hy : (fun a => φ (y a)) ∈ W)
    (a : Fin n) (ha : Module.finrank K W ≤ (a : ℕ)) :
    (((g⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R).mulVec y) a = 0 := by sorry
