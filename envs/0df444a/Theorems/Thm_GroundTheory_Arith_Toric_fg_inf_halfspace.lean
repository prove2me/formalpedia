-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_fg_inf_halfspace
-- name    : GroundTheory.Arith.Toric.fg_inf_halfspace
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:17.290994+00:00
-- url     : https://prove2.me/theorems/05b8e8ba-7752-48a6-ba8a-529cbf3b4988
-- title:
--   Toric: fg inf halfspace
-- statement:
--   The Toric construction uses the fg inf halfspace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L184-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L184-L189

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

theorem GroundTheory.Arith.Toric.fg_inf_halfspace {C : PointedCone 𝕜 V} (hC : C.FG) (g : Dual 𝕜 V) :
    (C ⊓ (positive 𝕜 𝕜).comap g).FG := by sorry
