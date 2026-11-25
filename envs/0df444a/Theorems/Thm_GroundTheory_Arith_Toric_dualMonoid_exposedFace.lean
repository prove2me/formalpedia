-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_dualMonoid_exposedFace
-- name    : GroundTheory.Arith.Toric.dualMonoid_exposedFace
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:55:05.255211+00:00
-- url     : https://prove2.me/theorems/8c338098-96e9-44a4-924f-d4580c595854
-- title:
--   Toric: dual Monoid exposed Face
-- statement:
--   The Toric construction uses the dual Monoid exposed Face property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ToricFaces.lean#L100-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ToricFaces.lean#L100-L120

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
omit [Module.Free ℤ N] [Module.Finite ℤ N]

theorem GroundTheory.Arith.Toric.dualMonoid_exposedFace {σ : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) {u : Dual ℤ N} (hu : u ∈ dualMonoid σ) :
    dualMonoid (exposedFace σ (toRealDual N u)) = dualMonoid σ ⊔ AddSubmonoid.closure {-u} := by sorry
