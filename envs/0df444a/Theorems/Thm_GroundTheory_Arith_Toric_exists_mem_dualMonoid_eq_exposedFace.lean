-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_exists_mem_dualMonoid_eq_exposedFace
-- name    : GroundTheory.Arith.Toric.exists_mem_dualMonoid_eq_exposedFace
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:55:51.26136+00:00
-- url     : https://prove2.me/theorems/0dbaa7e1-ad93-42d5-a195-0e95158b1bfa
-- title:
--   Toric: exists mem dual Monoid eq exposed Face
-- statement:
--   The Toric construction uses the exists mem dual Monoid eq exposed Face property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ToricFaces.lean#L90-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ToricFaces.lean#L90-L96

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_IsFaceOfIffExistsEqExposedFace
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ToricFaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone TensorProduct
variable {N : Type*} [AddCommGroup N]
variable [Module.Free ℤ N] [Module.Finite ℤ N]

theorem GroundTheory.Arith.Toric.exists_mem_dualMonoid_eq_exposedFace {σ τ : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) (hτ : τ.IsFaceOf σ) :
    ∃ u ∈ dualMonoid σ, τ = exposedFace σ (toRealDual N u) := by sorry
