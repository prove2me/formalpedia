-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_dualMonoid_anti
-- name    : GroundTheory.Arith.Toric.dualMonoid_anti
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:55:45.511375+00:00
-- url     : https://prove2.me/theorems/55b9cf67-ea9e-4839-b965-7a9daef88eae
-- title:
--   Toric: dual Monoid anti
-- statement:
--   The Toric construction uses the dual Monoid anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ToricFaces.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ToricFaces.lean#L38-L40

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

theorem GroundTheory.Arith.Toric.dualMonoid_anti {σ₁ σ₂ : PointedCone ℝ (ℝ ⊗[ℤ] N)} (h : σ₁ ≤ σ₂) :
    dualMonoid σ₂ ≤ dualMonoid σ₁ := by sorry
