-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_exists_heat_uniform_majorant
-- name    : OAI.TriangularHilbert.Heat.exists_heat_uniform_majorant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:49:47.787977+00:00
-- url     : https://prove2.me/theorems/ebeba126-e975-45b5-aac3-61a34df29caa
-- title:
--   An integrable majorant for the heat calculus over the plane of centres
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. For a triangle array $A$, mesh $h>0$, positions $u$, centres $p=(p_0,p_1,p_2)$ and variances $\sigma$, the heat star energies $\mathrm{heatEnergy}(v)$, their centre and variance derivatives ($\mathrm{heatFirst}$, $\mathrm{heatPure}$, $\mathrm{heatVariance}$), the Hessian costs $\mathrm{heatCost}(v,w)$ and the mixed Hessian terms $\mathrm{heatMixed}(v,w,z)$ are real numbers attached to each vertex. Centres with $p_0+p_1+p_2=d$ are parametrized by $\mathrm{chart}(i,d,z)$, $z\in\mathbb R^2$, and $\mathrm{planeIntegral}(f,d)=\int_{\mathbb R^2}f(\mathrm{chart}(2,d,z))\,dz$. Let $h>0$, $0<a\le b$ and $D\ge0$. Then there is a nonnegative integrable $B:\mathbb R^2\to\mathbb R$ such that for every chart $i$, every $|d|\le D$, every $z$ and all variances with $a\le\sigma_w\le b$, all heat quantities at the centres $\mathrm{chart}(i,d,z)$ are bounded by $B(z)$:
--   $$
--   \mathrm{HeatAtBounds}\bigl(A,h,u,\mathrm{chart}(i,d,z),\sigma,B(z)\bigr).
--   $$
--
--   This single majorant justifies all differentiations under the plane integral.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/HeatBound.lean#L87-L145

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uι
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.Heat.exists_heat_uniform_majorant (A : Three → Matrix ι ι ℂ) {h a b D : ℝ}
    (hh : 0 < h) (ha : 0 < a) (hab : a ≤ b) (hD : 0 ≤ D) (u : ι → ℝ) :
    ∃ B : (ℝ × ℝ) → ℝ, Integrable B ∧ (∀ z, 0 ≤ B z) ∧
      ∀ (i : Three) (d : ℝ) (z : ℝ × ℝ), |d| ≤ D → ∀ (σ : Three → ℝ),
      (∀ w, a ≤ σ w) → (∀ w, σ w ≤ b) → HeatAtBounds A h u (chart i d z) σ (B z) := by sorry
