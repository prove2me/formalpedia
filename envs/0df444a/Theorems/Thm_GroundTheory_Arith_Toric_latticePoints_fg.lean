-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_latticePoints_fg
-- name    : GroundTheory.Arith.Toric.latticePoints_fg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:26:54.624818+00:00
-- url     : https://prove2.me/theorems/a6ee6da6-6eeb-47c9-b686-c05331e9bb7b
-- title:
--   Toric: lattice Points fg
-- statement:
--   The Toric construction uses the lattice Points fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Lattice.lean#L243-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Lattice.lean#L243-L300

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

theorem GroundTheory.Arith.Toric.latticePoints_fg {τ : PointedCone ℝ (Dual ℝ (ℝ ⊗[ℤ] N))}
    (hτ : IsRationalPolyhedral (toRealDual N) τ) : (latticePoints (toRealDual N) τ).FG := by sorry
