-- Prove2me | Theorems.Thm_OAI_Release075_MarkedLineData_rectangular_nontriviality
-- name    : OAI.Release075.MarkedLineData.rectangular_nontriviality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:09:48.249976+00:00
-- url     : https://prove2.me/theorems/0a234906-f528-428d-acea-6e56158285c7
-- title:
--   Rectangular words are nontrivial in the marked-line presentation
-- statement:
--   Let $d$ be marked-line data over a prime $q$ with parameter $r>0$ (marks in $\mathbb F_q^{20}$ with projective directions, incidence girth greater than $12$, and enough incidences at non-exceptional points), and let $\Gamma$ be the presented group of the associated block presentation with generators $x_{i,u,v}$, $l_{b,u,j}$, $r_{b,v,k}$ and triangle relations $x_{i,u,v}=l_{b,u,c_1(i)+v}^{-1}r_{b,v,c_2(i)+u}$. Then every rectangular word in the $x$-generators of one label is nontrivial:
--   $$
--   x_{i,u,v}\,x_{i,u',v}^{-1}\,x_{i,u',v'}\,x_{i,u,v'}^{-1}\ne1\qquad(u\ne u',\ v\ne v').
--   $$
--
--   This is the nontriviality premise of the residual-finiteness obstruction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Rectangles.lean#L50-L88

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links

open OAI OAI.Release075 OAI.Release075.MarkedLineData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

theorem OAI.Release075.MarkedLineData.rectangular_nontriviality : d.RectangularNontriviality hr := by sorry
