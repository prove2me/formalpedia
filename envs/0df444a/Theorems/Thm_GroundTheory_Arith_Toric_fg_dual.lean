-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_fg_dual
-- name    : GroundTheory.Arith.Toric.fg_dual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:41.412968+00:00
-- url     : https://prove2.me/theorems/94889393-8da4-4e3e-a224-2e2ed7eecf4c
-- title:
--   Toric: fg dual
-- statement:
--   The Toric construction uses the fg dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L202-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L202-L206

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

theorem GroundTheory.Arith.Toric.fg_dual [FiniteDimensional 𝕜 N] (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) {C : PointedCone 𝕜 M}
    (hC : C.FG) : (dual p (C : Set M)).FG := by sorry
