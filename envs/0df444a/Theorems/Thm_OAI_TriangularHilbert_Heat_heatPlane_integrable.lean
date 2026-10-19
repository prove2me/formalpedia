-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_heatPlane_integrable
-- name    : OAI.TriangularHilbert.Heat.heatPlane_integrable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:52:58.619995+00:00
-- url     : https://prove2.me/theorems/7708b96e-51d5-439a-b0a7-9790bd723023
-- title:
--   Integrability of the heat calculus over the plane of centres
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. For a triangle array $A$, mesh $h>0$, positions $u$, centres $p=(p_0,p_1,p_2)$ and variances $\sigma$, the heat star energies $\mathrm{heatEnergy}(v)$, their centre and variance derivatives ($\mathrm{heatFirst}$, $\mathrm{heatPure}$, $\mathrm{heatVariance}$), the Hessian costs $\mathrm{heatCost}(v,w)$ and the mixed Hessian terms $\mathrm{heatMixed}(v,w,z)$ are real numbers attached to each vertex. Centres with $p_0+p_1+p_2=d$ are parametrized by $\mathrm{chart}(i,d,z)$, $z\in\mathbb R^2$, and $\mathrm{planeIntegral}(f,d)=\int_{\mathbb R^2}f(\mathrm{chart}(2,d,z))\,dz$. Let $h>0$ and all variances $\sigma_w>0$. Then for every centre sum $d$ and every chart $i$, all the functions
--   $$
--   z\longmapsto\mathrm{heatEnergy},\ \mathrm{heatFirst},\ \mathrm{heatPure},\ \mathrm{heatVariance},\ \mathrm{heatCost},\ \mathrm{heatMixed}\quad\text{at }p=\mathrm{chart}(i,d,z)
--   $$
--   are integrable on $\mathbb R^2$; in short, $\mathrm{HeatPlaneIntegrable}(A,h,u,d,\sigma)$ holds.
--
--   All plane integrals of the heat calculus are finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/PlaneIntegral.lean#L84-L105

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uι
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.Heat.heatPlane_integrable (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) :
    HeatPlaneIntegrable A h u d σ := by sorry
