-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_finiteType_toricAlgebra
-- name    : GroundTheory.Arith.Toric.finiteType_toricAlgebra
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:56:11.926814+00:00
-- url     : https://prove2.me/theorems/7d06e341-ce76-4598-8687-0b36c7376910
-- title:
--   Toric: finite Type toric Algebra
-- statement:
--   The Toric construction uses the finite Type toric Algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Affine.lean#L197-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Affine.lean#L197-L199

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ToricFaces
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Affine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry
universe u
variable {N : Type u} [AddCommGroup N] (k : Type u) [CommRing k]
variable {k}
variable [Module.Free ℤ N] [Module.Finite ℤ N]

theorem GroundTheory.Arith.Toric.finiteType_toricAlgebra {σ : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) : Algebra.FiniteType k (toricAlgebra k σ) := by sorry
