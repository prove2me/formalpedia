-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_rowStar_differentiableAt
-- name    : OAI.TriangularHilbert.Heat.rowStar_differentiableAt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:50:40.985696+00:00
-- url     : https://prove2.me/theorems/776b8df4-597b-48ef-9279-2e41c3ed8ef1
-- title:
--   Star rows depend differentiably on the triangle array
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. Let $E$ be a real normed space and $y\mapsto W(y)$ a family of triangle arrays whose three edge matrices $W(y)_v$ are differentiable at $x$. Then for every vertex $v$ the star row
--   $$
--   y\longmapsto\mathrm{rowStar}(W(y),v)=\Pi_v\cdot\mathrm{triangle}(W(y))
--   $$
--   is differentiable at $x$.
--
--   Hence heat Gram matrices are differentiable in any parameters on which the weighted arrays depend differentiably.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/HeatTime.lean#L83-L96

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uν uι uE
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology BigOperators
open Filter
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.Heat.rowStar_differentiableAt {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : E → Three → Matrix ι ι ℂ} {x : E} (hW : ∀ v, DifferentiableAt ℝ (fun y => W y v) x)
    (v : Three) : DifferentiableAt ℝ (fun y => rowStar (W y) v) x := by sorry
