-- Prove2me | Theorems.Thm_OAI_Release075_MarkedLineData_sphere_empty_of_noDipole
-- name    : OAI.Release075.MarkedLineData.sphere_empty_of_noDipole
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:14:59.100387+00:00
-- url     : https://prove2.me/theorems/ac5477b6-f083-4267-af45-c4e7474c51a9
-- title:
--   Dipole-free spheres over the marked-line presentation are empty
-- statement:
--   Let $d$ be marked-line data over a prime $q$ with parameter $r>0$ (marks in $\mathbb F_q^{20}$ with projective directions, incidence girth greater than $12$, and enough incidences at non-exceptional points), and let $\Gamma$ be the presented group of the associated block presentation with generators $x_{i,u,v}$, $l_{b,u,j}$, $r_{b,v,k}$ and triangle relations $x_{i,u,v}=l_{b,u,c_1(i)+v}^{-1}r_{b,v,c_2(i)+u}$. A triangle sphere is a finite labelled planar map (darts with a fixed-point-free reverse involution $r$ and a face permutation $n$ satisfying the Euler equality $\mathrm{cyc}(r)+\mathrm{cyc}(n)+\mathrm{cyc}(rn)=|\text{darts}|+2\,\mathrm{comp}$) all of whose faces are triangles of the face relation, with flip-compatible labels and colours constant along $rn$. A dipole is a pair of faces sharing an edge with mirrored labels. Every triangle sphere over the oriented edges and triangle faces of this presentation that has no dipole is empty, i.e. has
--   $$
--   |\text{darts}|=0 .
--   $$
--
--   Equivalently, every nonempty such sphere contains a cancellable pair of faces.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Spheres.lean#L235-L257

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
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres

open OAI OAI.Release075 OAI.Release075.MarkedLineData
open Equiv PermCycles
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

theorem OAI.Release075.MarkedLineData.sphere_empty_of_noDipole
    (D : TriangleSphere (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
      (d.presentation hr).TriangleFace) (hD : IsEmpty D.Dipole) : IsEmpty D.Dart := by sorry
