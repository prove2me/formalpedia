-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_trdeg_semigroupAlgebra_top
-- name    : GroundTheory.Arith.Toric.trdeg_semigroupAlgebra_top
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:55:18.505341+00:00
-- url     : https://prove2.me/theorems/d7793e95-be3f-504e-a195-0b8b50d93c2b
-- title:
--   Toric: trdeg semigroup Algebra top
-- statement:
--   The Toric construction uses the trdeg semigroup Algebra top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Dimension.lean#L85-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Dimension.lean#L85-L112

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Normal
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
universe u
open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry Algebra
variable {k G : Type u} [CommRing k] [IsDomain k] [AddCommGroup G] [Module.Free ℤ G]
variable [Module.Finite ℤ G]

theorem GroundTheory.Arith.Toric.trdeg_semigroupAlgebra_top :
    trdeg k (semigroupAlgebra k (⊤ : AddSubmonoid G)) = Module.finrank ℤ G := by sorry
