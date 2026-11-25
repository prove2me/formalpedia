-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_IsRationalPolyhedral_inf
-- name    : GroundTheory.Arith.Toric.IsRationalPolyhedral.inf
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:23:27.689646+00:00
-- url     : https://prove2.me/theorems/cd6bb27f-e186-449a-80c1-f56cb5f815b4
-- title:
--   Is Rational Polyhedral: inf
-- statement:
--   The Is Rational Polyhedral construction uses the inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Lattice.lean#L218-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Lattice.lean#L218-L227

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
variable {N : Type*} [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]

theorem GroundTheory.Arith.Toric.IsRationalPolyhedral.inf {σ σ' : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (h : IsRationalPolyhedral (toRealSpan N) σ) (h' : IsRationalPolyhedral (toRealSpan N) σ') :
    IsRationalPolyhedral (toRealSpan N) (σ ⊓ σ') := by sorry
