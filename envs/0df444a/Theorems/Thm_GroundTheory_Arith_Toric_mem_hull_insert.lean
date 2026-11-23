-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_mem_hull_insert
-- name    : GroundTheory.Arith.Toric.mem_hull_insert
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:46.144208+00:00
-- url     : https://prove2.me/theorems/9d116481-c51f-44ed-b4fc-898fc2d7b3e5
-- title:
--   Toric: mem hull insert
-- statement:
--   The Toric construction uses the mem hull insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L12-L19

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

theorem GroundTheory.Arith.Toric.mem_hull_insert {a x : V} {s : Set V} :
    x ∈ hull 𝕜 (insert a s) ↔ ∃ c : 𝕜, 0 ≤ c ∧ ∃ y ∈ hull 𝕜 s, x = c • a + y := by sorry
