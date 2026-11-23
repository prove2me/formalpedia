-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_nonneg_of_mem_hull
-- name    : GroundTheory.Arith.Toric.nonneg_of_mem_hull
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:36.681146+00:00
-- url     : https://prove2.me/theorems/8d5d9a07-28e1-4475-9eea-1a6457a450b4
-- title:
--   Toric: nonneg of mem hull
-- statement:
--   The Toric construction uses the nonneg of mem hull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L36-L40

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

theorem GroundTheory.Arith.Toric.nonneg_of_mem_hull {f : Dual 𝕜 V} {s : Set V} (hs : ∀ y ∈ s, 0 ≤ f y) {x : V}
    (hx : x ∈ hull 𝕜 s) : 0 ≤ f x := by sorry
