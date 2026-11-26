-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_transformed_image_plus_cone_implies_objective_eq_zero
-- name    : LowRankUnivariateSOS.transformed_image_plus_cone_implies_objective_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:39.501243+00:00
-- url     : https://prove2.me/theorems/865531d4-e7fc-5370-a666-71eb96c9c4dc
-- title:
--   Low Rank Univariate SOS: transformed image plus cone implies objective eq zero
-- statement:
--   This is the abstract certificate step behind condition (C2). If `p`
--    decomposes as an image term for some transformed pair `uImg` plus a sum of
--    kernel squares for the original pair `u`, and if the residual is orthogonal to
--    `im(A_{uImg})`, then the SOCP inequalities force the objective to be zero.
--    The proof is exactly the paper's image-plus-cone argument: the image part dies
--    by first-order criticality, the kernel terms are nonnegative by second-order
--    criticality, and `⟨σ(u),σ(u)-p⟩=0` closes the estimate.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/FactoredCase.lean#L81-L121
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/FactoredCase.lean#L81-L121

import Mathlib.Tactic.Linarith
import Definitions.Def_LowRankUnivariateSOS_Socp
import Definitions.Def_LowRankUnivariateSOS_H1Case
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]

theorem LowRankUnivariateSOS.transformed_image_plus_cone_implies_objective_eq_zero {p : Poly} {u uImg : UPair}
    (hsocp : IsSOCP B p u)
    (himg : ImageOrthogonalResidual B p u uImg)
    (hdecomp : ∃ imgPart : Poly, ∃ ws : Finset UPair,
      InImageA uImg imgPart ∧ (∀ w ∈ ws, InKerA u w) ∧ p = imgPart + ws.sum sigma2) :
    objective B p u = 0 := by sorry
