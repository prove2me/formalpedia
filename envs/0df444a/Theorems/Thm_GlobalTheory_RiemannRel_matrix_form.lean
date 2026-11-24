-- Prove2me | Theorems.Thm_GlobalTheory_RiemannRel_matrix_form
-- name    : GlobalTheory.RiemannRel.matrix_form
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:24:40.502273+00:00
-- url     : https://prove2.me/theorems/2614d879-cee4-49e7-a03b-467527201201
-- title:
--   Riemann Rel: matrix form
-- statement:
--   The Riemann Rel construction uses the matrix form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSiegelPeriodOfSymplecticBasis.lean#L28-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSiegelPeriodOfSymplecticBasis.lean#L28-L113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_GeomIntSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSiegelPeriodOfSymplecticBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
open Matrix
open GlobalTheory GlobalTheory.RiemannRel

theorem GlobalTheory.RiemannRel.matrix_form {h : ℕ} (Hm L M : Matrix (Fin h) (Fin h) ℂ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin h → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (hG : (Mᵀ * Hm * M.map star).map Complex.im = 0)
    (hA : (Lᵀ * Hm * M.map star).map Complex.im = 1)
    (hB : (Lᵀ * Hm * L.map star).map Complex.im = 0) :
    IsUnit M.det ∧ (M⁻¹ * L).IsSymm ∧ ((M⁻¹ * L).map Complex.im).PosDef := by sorry
