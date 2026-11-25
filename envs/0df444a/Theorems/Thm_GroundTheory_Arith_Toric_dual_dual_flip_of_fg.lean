-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_dual_dual_flip_of_fg
-- name    : GroundTheory.Arith.Toric.dual_dual_flip_of_fg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:34.822668+00:00
-- url     : https://prove2.me/theorems/a9825f35-5c2e-4f35-86c0-c7ebd8f64d2a
-- title:
--   Toric: dual dual flip of fg
-- statement:
--   The Toric construction uses the dual dual flip of fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L208-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L208-L217

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {V W : Type*} [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
variable {M N : Type*} [AddCommGroup M] [Module 𝕜 M] [AddCommGroup N] [Module 𝕜 N]

theorem GroundTheory.Arith.Toric.dual_dual_flip_of_fg (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) (hp : Function.Surjective p)
    {C : PointedCone 𝕜 N} (hC : C.FG) : dual p (dual p.flip (C : Set N)) = C := by sorry
