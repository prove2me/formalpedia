-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_sum
-- name    : GroundTheory.Arith.Toric.LowerBound.sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:35:56.288085+00:00
-- url     : https://prove2.me/theorems/cb66b930-c367-4258-ac5c-007665cd733f
-- title:
--   Lower Bound: sum
-- statement:
--   The Lower Bound construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Normal.lean#L43-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Normal.lean#L43-L50

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Affine
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Normal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
universe u
open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry Polynomial
variable {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G] (φ : G →+ ℤ)
variable {φ}

theorem GroundTheory.Arith.Toric.LowerBound.sum {ι : Type*} (s : Finset ι) {f : ι → AddMonoidAlgebra k G} {a : ℤ}
    (hf : ∀ i ∈ s, LowerBound φ (f i) a) : LowerBound φ (∑ i ∈ s, f i) a := by sorry
