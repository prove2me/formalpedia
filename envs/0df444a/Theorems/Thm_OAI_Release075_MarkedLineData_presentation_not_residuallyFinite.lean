-- Prove2me | Theorems.Thm_OAI_Release075_MarkedLineData_presentation_not_residuallyFinite
-- name    : OAI.Release075.MarkedLineData.presentation_not_residuallyFinite
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:49:17.835766+00:00
-- url     : https://prove2.me/theorems/d26b5256-2b58-4a93-8d9c-c9c7a74382db
-- title:
--   The block presentation from marked-line data is not residually finite
-- statement:
--   Let $d$ be marked-line data over a prime $q\ge200$ with parameter $0<r<q$: injective marks in a grid of $q/100$ scalars in $\mathbb F_q^{20}$ with projective directions, an exceptional set $E$ such that every other point has at least $4r^2$ punctured incidences, and the budget $4(2q^{20}+r|E|)<|\text{labels}|\cdot r$. Let $\Gamma$ be the block presentation built from $d$. If the generators $x_{i,u,v}$ of $\Gamma$ satisfy rectangular nontriviality, i.e.
--   $$
--   x_{i,u,v}\,x_{i,u',v}^{-1}\,x_{i,u',v'}\,x_{i,u,v'}^{-1}\ne1\qquad(u\ne u',\ v\ne v'),
--   $$
--   then $\Gamma$ is not residually finite.
--
--   The rectangular nontriviality hypothesis is established separately from the small-cancellation geometry.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Presentation.lean#L467-L482

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation

open OAI OAI.Release075 OAI.Release075.MarkedLineData
open scoped BigOperators
attribute [local instance] OAI.Release075.instDecidableEq_oAI
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)

theorem OAI.Release075.MarkedLineData.presentation_not_residuallyFinite (hr : 0 < r) (hq : r < q) (hq200 : 200 ≤ q)
    (hrect : d.RectangularNontriviality hr) :
    ¬ Group.ResiduallyFinite (d.presentation hr).GroupType := by sorry
