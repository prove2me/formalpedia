-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_isRationalPolyhedral_top
-- name    : GroundTheory.Arith.Toric.isRationalPolyhedral_top
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:26:51.111816+00:00
-- url     : https://prove2.me/theorems/07b4afca-f3b9-4769-8d5e-f1dd29e1b493
-- title:
--   Toric: is Rational Polyhedral top
-- statement:
--   The Toric construction uses the is Rational Polyhedral top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Lattice.lean#L153-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Lattice.lean#L153-L164

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
variable (N : Type*) [AddCommGroup N]
variable {N}
variable [Module.Free ℤ N] [Module.Finite ℤ N]

theorem GroundTheory.Arith.Toric.isRationalPolyhedral_top :
    IsRationalPolyhedral (toRealSpan N) (⊤ : PointedCone ℝ (ℝ ⊗[ℤ] N)) := by sorry
