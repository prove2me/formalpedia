-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_image_orthogonal_of_peeling_path
-- name    : LowRankUnivariateSOS.image_orthogonal_of_peeling_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:04.243556+00:00
-- url     : https://prove2.me/theorems/123c2daa-3629-5548-b519-1755e8e6ba3d
-- title:
--   Low Rank Univariate SOS: image orthogonal of peeling path
-- statement:
--   Orthogonality propagates along an entire peeling path by iterating the
--    one-step propagation lemma. This is the abstract form of the paper's repeated
--    factor-peeling argument.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PeelingStep.lean#L377-L386
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PeelingStep.lean#L377-L386

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
import Definitions.Def_LowRankUnivariateSOS_PeelingStep
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}

theorem LowRankUnivariateSOS.image_orthogonal_of_peeling_path {p : Poly} {u uStart uEnd : UPair}
    (hsocp : IsSOCP B p u)
    (hstart : ImageOrthogonalResidual B p u uStart)
    (hpath : PeelingPath u uStart uEnd) :
    ImageOrthogonalResidual B p u uEnd := by sorry
