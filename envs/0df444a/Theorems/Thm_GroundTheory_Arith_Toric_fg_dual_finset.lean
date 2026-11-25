-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_fg_dual_finset
-- name    : GroundTheory.Arith.Toric.fg_dual_finset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:01.877715+00:00
-- url     : https://prove2.me/theorems/4b212cb1-1294-42d7-a35a-428e360078b5
-- title:
--   Toric: fg dual finset
-- statement:
--   The Toric construction uses the fg dual finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L193-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L193-L200

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

theorem GroundTheory.Arith.Toric.fg_dual_finset [FiniteDimensional 𝕜 N] (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) (s : Finset M) :
    (dual p (s : Set M)).FG := by sorry
