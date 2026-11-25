-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_mem_dualMonoid
-- name    : GroundTheory.Arith.Toric.mem_dualMonoid
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:23:30.894285+00:00
-- url     : https://prove2.me/theorems/11382d29-04e4-43a7-9c03-96bbed92974b
-- title:
--   Toric: mem dual Monoid
-- statement:
--   The Toric construction uses the mem dual Monoid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Lattice.lean#L238-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Lattice.lean#L238-L239

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

theorem GroundTheory.Arith.Toric.mem_dualMonoid {σ : PointedCone ℝ (ℝ ⊗[ℤ] N)} {m : Dual ℤ N} :
    m ∈ dualMonoid σ ↔ ∀ x ∈ σ, 0 ≤ toRealDual N m x := by sorry
