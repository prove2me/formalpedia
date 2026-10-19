-- Prove2me | Theorems.Thm_OAI_Release075_MarkedLineData_exists_lifted_linear_filling
-- name    : OAI.Release075.MarkedLineData.exists_lifted_linear_filling
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:13:16.42958+00:00
-- url     : https://prove2.me/theorems/a5dd227f-a9a4-485a-80dc-390644f72bd0
-- title:
--   Fillable lifted words have fillings of linear size
-- statement:
--   Let $d$ be marked-line data over a prime $q$ with parameter $r>0$ (marks in $\mathbb F_q^{20}$ with projective directions, incidence girth greater than $12$, and enough incidences at non-exceptional points), and let $\Gamma$ be the presented group of the associated block presentation with generators $x_{i,u,v}$, $l_{b,u,j}$, $r_{b,v,k}$ and triangle relations $x_{i,u,v}=l_{b,u,c_1(i)+v}^{-1}r_{b,v,c_2(i)+u}$. Consider words of lifted edges (oriented edges together with coordinates in $\Gamma$) and lifted faces, whose three corners are glued at equal group coordinates. If such a word $w$ is fillable, then it has a filling $D$ with
--   $$
--   \mathrm{active}(D)\le19\,|w| .
--   $$
--
--   This is the linear isoperimetric inequality in the lifted (Cayley complex) setting.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/LiftedFilling.lean#L311-L332

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
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling

open OAI OAI.Release075 OAI.Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)
variable {w : List (d.presentation hr).LiftedEdge}

theorem OAI.Release075.MarkedLineData.exists_lifted_linear_filling (hf : Fillable (d.presentation hr).liftedFlip
    (d.presentation hr).liftedTarget (d.presentation hr).LiftedFace w) :
    ∃ D : TriangleFilling (d.presentation hr).liftedFlip (d.presentation hr).liftedTarget
      (d.presentation hr).LiftedFace w, D.activeCount ≤ 19*w.length := by sorry
