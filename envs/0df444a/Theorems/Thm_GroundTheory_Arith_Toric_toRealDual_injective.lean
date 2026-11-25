-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_toRealDual_injective
-- name    : GroundTheory.Arith.Toric.toRealDual_injective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:55:47.896225+00:00
-- url     : https://prove2.me/theorems/4221bdfc-4342-4411-9016-2e3ba6e6a67c
-- title:
--   Toric: to Real Dual injective
-- statement:
--   The Toric construction uses the to Real Dual injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ToricFaces.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ToricFaces.lean#L31-L36

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_IsFaceOfIffExistsEqExposedFace
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ToricFaces
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
variable {N : Type*} [AddCommGroup N]

theorem GroundTheory.Arith.Toric.toRealDual_injective : Function.Injective (toRealDual N) := by sorry
