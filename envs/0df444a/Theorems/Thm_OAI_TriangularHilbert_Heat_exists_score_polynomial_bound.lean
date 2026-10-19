-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_exists_score_polynomial_bound
-- name    : OAI.TriangularHilbert.Heat.exists_score_polynomial_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:48:29.743249+00:00
-- url     : https://prove2.me/theorems/d63446a9-1e0f-4e94-9e7d-68cb05bd951b
-- title:
--   Polynomial bounds for scores over the plane of centres
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. Let $u$ be finitely many positions, $a>0$ and $D\ge0$. Centres are given by a chart, $p=\mathrm{chart}(i,d,z)$ with $|d|\le D$ and $z\in\mathbb R^2$. Then there is $C\ge0$ such that for all charts, all variances $\sigma_w\ge a$, all vertices $w$ and all positions $u_j$,
--   $$
--   \Bigl|\frac{u_j-p_w}{\sigma_w}\Bigr|\le C\,(1+z_1^2)(1+z_2^2),\qquad\Bigl|\Bigl(\frac{u_j-p_w}{\sigma_w}\Bigr)^2-\frac1{\sigma_w}\Bigr|\le(C^2+a^{-1})(1+z_1^2)^2(1+z_2^2)^2 .
--   $$
--
--   Scores grow at most polynomially in the free coordinates of the centres.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/PlaneDom.lean#L138-L175

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uι
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem OAI.TriangularHilbert.Heat.exists_score_polynomial_bound (u : ι → ℝ) {a D : ℝ} (ha : 0 < a) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Three) (d : ℝ) (z : ℝ × ℝ), |d| ≤ D →
      ∀ (σ : Three → ℝ), (∀ w, a ≤ σ w) → ∀ w j,
        |score (u j) (chart i d z w) (σ w)| ≤ C * planePoly z ∧
        |score (u j) (chart i d z w) (σ w)^2 - (σ w)⁻¹| ≤ (C^2+a⁻¹) * planePoly z^2 := by sorry
