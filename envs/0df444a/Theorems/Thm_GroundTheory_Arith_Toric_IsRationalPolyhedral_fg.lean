-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_IsRationalPolyhedral_fg
-- name    : GroundTheory.Arith.Toric.IsRationalPolyhedral.fg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:23:27.653225+00:00
-- url     : https://prove2.me/theorems/1dcc5328-c887-45ae-a100-2e830c2d75e5
-- title:
--   Is Rational Polyhedral: fg
-- statement:
--   The Is Rational Polyhedral construction uses the fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Lattice.lean#L70-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Lattice.lean#L70-L74

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
variable {L E : Type*} [AddCommGroup L] [AddCommGroup E] [Module ℝ E]

theorem GroundTheory.Arith.Toric.IsRationalPolyhedral.fg {ι : L →ₗ[ℤ] E} {σ : PointedCone ℝ E}
    (hσ : IsRationalPolyhedral ι σ) : σ.FG := by sorry
