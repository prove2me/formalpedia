-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_image_orthogonal_self_of_focp
-- name    : LowRankUnivariateSOS.image_orthogonal_self_of_focp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:10.844255+00:00
-- url     : https://prove2.me/theorems/0615346e-62df-5d2d-8c39-0a63b2aa25cd
-- title:
--   Low Rank Univariate SOS: image orthogonal self of focp
-- statement:
--   A FOCP is automatically orthogonal to its own image: this is just the
--    first-order condition `\eqref{eq:gradA}` rewritten as a statement about the
--    entire image of `A_u`.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PeelingStep.lean#L110-L114
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PeelingStep.lean#L110-L114

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
import Definitions.Def_LowRankUnivariateSOS_PeelingStep
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}

theorem LowRankUnivariateSOS.image_orthogonal_self_of_focp {p : Poly} {u : UPair} (hfocp : IsFOCP B p u) :
    ImageOrthogonalResidual B p u u := by sorry
