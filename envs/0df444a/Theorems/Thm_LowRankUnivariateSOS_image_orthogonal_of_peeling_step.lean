-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_image_orthogonal_of_peeling_step
-- name    : LowRankUnivariateSOS.image_orthogonal_of_peeling_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:29.189349+00:00
-- url     : https://prove2.me/theorems/71a79e5a-4d4e-55c8-8063-552f1495b5d7
-- title:
--   Low Rank Univariate SOS: image orthogonal of peeling step
-- statement:
--   Orthogonality propagates across one peeling step: if the residual is
--    already orthogonal to the previous image, and every element of the next image
--    has a peeling witness, then it is also orthogonal to the next image.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PeelingStep.lean#L258-L265
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PeelingStep.lean#L258-L265

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
import Definitions.Def_LowRankUnivariateSOS_PeelingStep
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}

theorem LowRankUnivariateSOS.image_orthogonal_of_peeling_step {p : Poly} {u uImgPrev uImgNext : UPair}
    (hsocp : IsSOCP B p u)
    (hprev : ImageOrthogonalResidual B p u uImgPrev)
    (hstep : HasPeelingWitness u uImgPrev uImgNext) :
    ImageOrthogonalResidual B p u uImgNext := by sorry
