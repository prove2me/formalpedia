-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_adjoin_genX_genY
-- name    : GroundTheory.Arith.Abelian.adjoin_genX_genY
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:21.880413+00:00
-- url     : https://prove2.me/theorems/4264460e-eaf0-4547-a96a-8145df2ca875
-- title:
--   Abelian: adjoin gen X gen Y
-- statement:
--   The Abelian construction uses the adjoin gen X gen Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/FunctionFieldPoint.lean#L158-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/FunctionFieldPoint.lean#L158-L177

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

theorem GroundTheory.Arith.Abelian.adjoin_genX_genY : IntermediateField.adjoin F {genX W, genY W} = ⊤ := by sorry
