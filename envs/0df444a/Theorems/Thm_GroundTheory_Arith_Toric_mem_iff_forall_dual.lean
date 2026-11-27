-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_mem_iff_forall_dual
-- name    : GroundTheory.Arith.Toric.mem_iff_forall_dual
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:52:40.990059+00:00
-- url     : https://prove2.me/theorems/a6b52008-f6f0-4886-a7a6-e69e025ee3cb
-- title:
--   Toric: mem iff forall dual
-- statement:
--   The Toric construction uses the mem iff forall dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L93-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L93-L98

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

theorem GroundTheory.Arith.Toric.mem_iff_forall_dual {C : PointedCone 𝕜 V} (hC : C.FG) {x : V} :
    x ∈ C ↔ ∀ f : Dual 𝕜 V, (∀ y ∈ C, 0 ≤ f y) → 0 ≤ f x := by sorry
