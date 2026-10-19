-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_planeCost_neighbors
-- name    : OAI.TriangularHilbert.Heat.planeCost_neighbors
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:54:28.063834+00:00
-- url     : https://prove2.me/theorems/7ed2be09-4cba-4661-9948-b8f42e1ff327
-- title:
--   Neighbouring Hessian costs are dominated by the own cost
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. For a triangle array $A$, mesh $h>0$, positions $u$, centres $p=(p_0,p_1,p_2)$ and variances $\sigma$, the heat star energies $\mathrm{heatEnergy}(v)$, their centre and variance derivatives ($\mathrm{heatFirst}$, $\mathrm{heatPure}$, $\mathrm{heatVariance}$), the Hessian costs $\mathrm{heatCost}(v,w)$ and the mixed Hessian terms $\mathrm{heatMixed}(v,w,z)$ are real numbers attached to each vertex. Centres with $p_0+p_1+p_2=d$ are parametrized by $\mathrm{chart}(i,d,z)$, $z\in\mathbb R^2$, and $\mathrm{planeIntegral}(f,d)=\int_{\mathbb R^2}f(\mathrm{chart}(2,d,z))\,dz$. Let $h>0$ and all $\sigma_a>0$. For every vertex $w$,
--   $$
--   \sum_{v\ne w}\mathrm{planeIntegral}\bigl(\mathrm{heatCost}(\cdot,v,w)\bigr)\le\sqrt2\ \mathrm{planeIntegral}\bigl(\mathrm{heatCost}(\cdot,w,w)\bigr).
--   $$
--
--   Moving the centre $p_w$ costs the two neighbouring stars at most $\sqrt2$ times what it costs the star at $w$ itself.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/PlaneTime.lean#L100-L117

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
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.Heat.planeCost_neighbors (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ a, 0 < σ a) (w : Three) :
    (∑ v, if v = w then 0 else planeIntegral (fun p => heatCost A h u p σ v w) d) ≤
      Real.sqrt 2 * planeIntegral (fun p => heatCost A h u p σ w w) d := by sorry
