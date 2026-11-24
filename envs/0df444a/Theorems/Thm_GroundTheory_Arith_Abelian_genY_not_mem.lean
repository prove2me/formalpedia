-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_genY_not_mem
-- name    : GroundTheory.Arith.Abelian.genY_not_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:38.145443+00:00
-- url     : https://prove2.me/theorems/b11f9d3d-ec26-4f21-91c7-8b1de1067de6
-- title:
--   Abelian: gen Y not mem
-- statement:
--   The Abelian construction uses the gen Y not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/FunctionFieldPoint.lean#L144-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/FunctionFieldPoint.lean#L144-L156

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem GroundTheory.Arith.Abelian.genY_not_mem : genY W ∉ IntermediateField.adjoin F {genX W} := by sorry
