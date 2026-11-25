-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_dual_dual_eq_self
-- name    : GroundTheory.Arith.Toric.dual_dual_eq_self
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:26:47.223259+00:00
-- url     : https://prove2.me/theorems/894e9e50-77c4-4f98-b355-0513b1ec7d81
-- title:
--   Toric: dual dual eq self
-- statement:
--   The Toric construction uses the dual dual eq self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Lattice.lean#L201-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Lattice.lean#L201-L203

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

theorem GroundTheory.Arith.Toric.dual_dual_eq_self {σ : PointedCone ℝ V} (hσ : σ.FG) :
    dual (LinearMap.id : Dual ℝ V →ₗ[ℝ] Dual ℝ V) (dual (Dual.eval ℝ V) (σ : Set V)) = σ := by sorry
