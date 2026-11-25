-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_mem_hull_image_finset_iff
-- name    : GroundTheory.Arith.Toric.mem_hull_image_finset_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:27:39.728107+00:00
-- url     : https://prove2.me/theorems/16dfdc30-3f12-489c-a324-854498573b76
-- title:
--   Toric: mem hull image finset iff
-- statement:
--   The Toric construction uses the mem hull image finset iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Lattice.lean#L13-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Lattice.lean#L13-L37

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone TensorProduct
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

theorem GroundTheory.Arith.Toric.mem_hull_image_finset_iff {ι : Type*} [DecidableEq ι] (T : Finset ι) (v : ι → E)
    {x : E} : x ∈ hull 𝕜 (v '' T) ↔ ∃ c : ι → 𝕜, (∀ i, 0 ≤ c i) ∧ ∑ i ∈ T, c i • v i = x := by sorry
