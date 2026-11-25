-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_dualMonoid_fg
-- name    : GroundTheory.Arith.Toric.dualMonoid_fg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:26:54.375802+00:00
-- url     : https://prove2.me/theorems/24348f5e-fb50-418a-bd2c-23a78fa07ec0
-- title:
--   Toric: dual Monoid fg
-- statement:
--   The Toric construction uses the dual Monoid fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Lattice.lean#L302-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Lattice.lean#L302-L304

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
variable {N : Type*} [AddCommGroup N]
variable [Module.Free ℤ N] [Module.Finite ℤ N]

theorem GroundTheory.Arith.Toric.dualMonoid_fg {σ : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) : (dualMonoid σ).FG := by sorry
