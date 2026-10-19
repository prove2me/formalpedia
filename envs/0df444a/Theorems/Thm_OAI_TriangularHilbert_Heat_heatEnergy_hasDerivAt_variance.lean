-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_heatEnergy_hasDerivAt_variance
-- name    : OAI.TriangularHilbert.Heat.heatEnergy_hasDerivAt_variance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:45:49.929996+00:00
-- url     : https://prove2.me/theorems/463f7ff4-df08-42ba-8aef-75bad3bca982
-- title:
--   Variance derivative of a heat star energy
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. Let $h>0$ and all variances $\sigma_w>0$. For vertices $v,w$, the heat energy $\mathrm{heatEnergy}(v)=E(\mathrm{starGram}(\mathrm{heatArray},v))$ is differentiable in the variance $\sigma_w$, with
--   $$
--   \frac{\partial}{\partial\sigma_w}\mathrm{heatEnergy}(v)=\mathrm{heatVariance}(v,w)=\frac12\nabla E(\mathrm{localGram}(v,w))\bigl[\mathrm{localSecond}(v,w)\bigr].
--   $$
--
--   The energy follows the heat equation through the variance derivative of its weights.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/HeatStar.lean#L117-L132

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uι
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
open Filter
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.Heat.heatEnergy_hasDerivAt_variance (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    HasDerivAt (fun q => heatEnergy A h u p (Function.update σ w q) v)
      (heatVariance A h u p σ v w) (σ w) := by sorry
