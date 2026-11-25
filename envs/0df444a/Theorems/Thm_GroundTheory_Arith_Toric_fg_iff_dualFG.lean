-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_fg_iff_dualFG
-- name    : GroundTheory.Arith.Toric.fg_iff_dualFG
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:52:59.374667+00:00
-- url     : https://prove2.me/theorems/5d44c7f0-1f13-4e7e-9892-e328394e5831
-- title:
--   Toric: fg iff dual FG
-- statement:
--   The Toric construction uses the fg iff dual FG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L219-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L219-L231

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

theorem GroundTheory.Arith.Toric.fg_iff_dualFG [FiniteDimensional 𝕜 M] [FiniteDimensional 𝕜 N]
    (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) (hp : Function.Surjective p) {C : PointedCone 𝕜 N} :
    C.FG ↔ C.DualFG p := by sorry
