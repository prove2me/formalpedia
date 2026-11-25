-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_bot_isFaceOf_iff
-- name    : GroundTheory.Arith.Toric.bot_isFaceOf_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:49:28.455112+00:00
-- url     : https://prove2.me/theorems/a5c6be60-5846-4f9f-a9a8-5e1c27de64da
-- title:
--   Toric: bot is Face Of iff
-- statement:
--   The Toric construction uses the bot is Face Of iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/IsFaceOfIffExistsEqExposedFace.lean#L369-L383
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/IsFaceOfIffExistsEqExposedFace.lean#L369-L383

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_IsFaceOfIffExistsEqExposedFace
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
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]

theorem GroundTheory.Arith.Toric.bot_isFaceOf_iff {σ : PointedCone 𝕜 V} :
    (⊥ : PointedCone 𝕜 V).IsFaceOf σ ↔ (σ : ConvexCone 𝕜 V).Salient := by sorry
