-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_IsRationalPolyhedral_sup
-- name    : GroundTheory.Arith.Toric.IsRationalPolyhedral.sup
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:23:30.644032+00:00
-- url     : https://prove2.me/theorems/c1e395b5-2845-4fa6-a432-5969299b8c57
-- title:
--   Is Rational Polyhedral: sup
-- statement:
--   The Is Rational Polyhedral construction uses the sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Lattice.lean#L205-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Lattice.lean#L205-L210

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
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem GroundTheory.Arith.Toric.IsRationalPolyhedral.sup {L : Type*} [AddCommGroup L] [DecidableEq L] {ι : L →ₗ[ℤ] V}
    {σ σ' : PointedCone ℝ V} (h : IsRationalPolyhedral ι σ) (h' : IsRationalPolyhedral ι σ') :
    IsRationalPolyhedral ι (σ ⊔ σ') := by sorry
