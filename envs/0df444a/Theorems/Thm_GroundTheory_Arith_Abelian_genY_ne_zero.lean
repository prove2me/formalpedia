-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_genY_ne_zero
-- name    : GroundTheory.Arith.Abelian.genY_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:31.838959+00:00
-- url     : https://prove2.me/theorems/5ced96a9-eb58-44e0-ae62-bbe4b8a2e087
-- title:
--   Abelian: gen Y ne zero
-- statement:
--   The Abelian construction uses the gen Y ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/FunctionFieldPoint.lean#L137-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/FunctionFieldPoint.lean#L137-L142

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

theorem GroundTheory.Arith.Abelian.genY_ne_zero : genY W ≠ 0 := by sorry
