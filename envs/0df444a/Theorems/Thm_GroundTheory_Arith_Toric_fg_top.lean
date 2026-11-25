-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_fg_top
-- name    : GroundTheory.Arith.Toric.fg_top
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:06.021092+00:00
-- url     : https://prove2.me/theorems/5a5db593-74d8-44c5-ab75-a682004e08ba
-- title:
--   Toric: fg top
-- statement:
--   The Toric construction uses the fg top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L100-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L100-L121

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

theorem GroundTheory.Arith.Toric.fg_top [FiniteDimensional 𝕜 V] : (⊤ : PointedCone 𝕜 V).FG := by sorry
