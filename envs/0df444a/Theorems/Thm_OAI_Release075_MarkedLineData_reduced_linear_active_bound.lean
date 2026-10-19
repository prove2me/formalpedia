-- Prove2me | Theorems.Thm_OAI_Release075_MarkedLineData_reduced_linear_active_bound
-- name    : OAI.Release075.MarkedLineData.reduced_linear_active_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:11:02.118839+00:00
-- url     : https://prove2.me/theorems/fa7b84d4-b4df-4669-8574-32042c2bef77
-- title:
--   Dipole-free fillings have linearly many darts
-- statement:
--   Let $d$ be marked-line data over a prime $q$ with parameter $r>0$ (marks in $\mathbb F_q^{20}$ with projective directions, incidence girth greater than $12$, and enough incidences at non-exceptional points), and let $\Gamma$ be the presented group of the associated block presentation with generators $x_{i,u,v}$, $l_{b,u,j}$, $r_{b,v,k}$ and triangle relations $x_{i,u,v}=l_{b,u,c_1(i)+v}^{-1}r_{b,v,c_2(i)+u}$. A triangle filling of a word is a finite labelled planar map (darts with a fixed-point-free reverse involution $r$ and a face permutation $n$ satisfying the Euler equality) whose boundary cycle spells the word and whose other faces, in the boundary's components, are triangles of the face relation. A dipole is a pair of interior triangles sharing an edge with mirrored labels; the active count is the number of darts in components meeting the boundary. If a filling $D$ of a word $w$ of oriented edges has no dipole and nonempty boundary, then
--   $$
--   \mathrm{active}(D)+36\le19\,|w| .
--   $$
--
--   This is a linear isoperimetric inequality for dipole-free diagrams.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Rectangles.lean#L124-L142

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
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)
variable {w : List (d.presentation hr).OrientedEdge}
variable (D : TriangleFilling (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
  (d.presentation hr).TriangleFace w) (b : D.Dart) (hb : b ∈ D.boundary)

include b hb in
theorem OAI.Release075.MarkedLineData.reduced_linear_active_bound (hD : IsEmpty D.Dipole) :
    D.activeCount + 36 ≤ 19*w.length := by sorry
