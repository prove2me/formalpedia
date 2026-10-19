-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_continuous_heatRow_param
-- name    : OAI.TriangularHilbert.Heat.continuous_heatRow_param
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:03:39.582583+00:00
-- url     : https://prove2.me/theorems/54646f7e-0636-4706-bbee-64b58a40cf09
-- title:
--   Heat star rows depend continuously on centres and variances
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. Let $E$ be a topological space and $t\mapsto p(t)$, $t\mapsto\sigma(t)$ continuous families of centres and variances with $\sigma(t)_w>0$. Then for every vertex $v$,
--   $$
--   t\longmapsto\mathrm{rowStar}\bigl(\mathrm{heatArray}(A,h,u,p(t),\sigma(t)),v\bigr)
--   $$
--   is continuous.
--
--   Heat star rows vary continuously with the heat parameters.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/JointHeat.lean#L41-L59

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
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uι uE
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.Heat.continuous_heatRow_param {E : Type uE} [TopologicalSpace E]
    (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (v : Three) :
    Continuous (fun t => rowStar (heatArray A h u (p t) (σ t)) v) := by sorry
