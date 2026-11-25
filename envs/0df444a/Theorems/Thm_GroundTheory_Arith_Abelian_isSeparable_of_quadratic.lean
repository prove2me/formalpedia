-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_isSeparable_of_quadratic
-- name    : GroundTheory.Arith.Abelian.isSeparable_of_quadratic
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:34:41.110539+00:00
-- url     : https://prove2.me/theorems/38bf5960-2853-4e5b-86eb-a84243760fdb
-- title:
--   Abelian: is Separable of quadratic
-- statement:
--   The Abelian construction uses the is Separable of quadratic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Isogeny.lean#L263-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Isogeny.lean#L263-L285

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
universe u
variable {F : Type u} [Field F]

theorem GroundTheory.Arith.Abelian.isSeparable_of_quadratic {L K : Type*} [Field L] [Field K] [Algebra L K] {y : K} (b c : L)
    (hy : y ^ 2 + algebraMap L K b * y - algebraMap L K c = 0)
    (hD' : algebraMap L K b ^ 2 + 4 * algebraMap L K c ≠ 0) :
    IsSeparable L y := by sorry
