-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_IsRationalPolyhedral_predual
-- name    : GroundTheory.Arith.Toric.IsRationalPolyhedral.predual
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:26:56.205809+00:00
-- url     : https://prove2.me/theorems/4be66246-974d-4d0f-8181-f8af427391f3
-- title:
--   Is Rational Polyhedral: predual
-- statement:
--   The Is Rational Polyhedral construction uses the predual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Lattice.lean#L180-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Lattice.lean#L180-L193

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice
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
variable (N : Type*) [AddCommGroup N]
variable {N}
variable [Module.Free ℤ N] [Module.Finite ℤ N]

theorem GroundTheory.Arith.Toric.IsRationalPolyhedral.predual {τ : PointedCone ℝ (Dual ℝ (ℝ ⊗[ℤ] N))}
    (hτ : IsRationalPolyhedral (toRealDual N) τ) :
    IsRationalPolyhedral (toRealSpan N)
      (PointedCone.dual (LinearMap.id : Dual ℝ (ℝ ⊗[ℤ] N) →ₗ[ℝ] Dual ℝ (ℝ ⊗[ℤ] N)) (τ : Set _)) := by sorry
