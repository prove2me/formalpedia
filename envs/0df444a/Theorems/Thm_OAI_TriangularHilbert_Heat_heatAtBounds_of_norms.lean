-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_heatAtBounds_of_norms
-- name    : OAI.TriangularHilbert.Heat.heatAtBounds_of_norms
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:49:10.945722+00:00
-- url     : https://prove2.me/theorems/e2af7ceb-6af0-4eb4-b82b-0dccf6e53d5c
-- title:
--   Bounds on heat energies and derivatives from carrier and score norms
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. For a triangle array $A$, mesh $h>0$, positions $u$, centres $p=(p_0,p_1,p_2)$ and variances $\sigma$, the heat star energies $\mathrm{heatEnergy}(v)$, their centre and variance derivatives ($\mathrm{heatFirst}$, $\mathrm{heatPure}$, $\mathrm{heatVariance}$), the Hessian costs $\mathrm{heatCost}(v,w)$ and the mixed Hessian terms $\mathrm{heatMixed}(v,w,z)$ are real numbers attached to each vertex. Let all $\sigma_w>0$. Suppose the carriers (star rows and their adjoints) satisfy $\|\mathrm{carrier}(v,w)\|^3\le E$. Suppose the diagonal score masks satisfy $\|\operatorname{diag}(\mathrm{score}_w)\|\le L$ and $\|\operatorname{diag}(\mathrm{score}_w^2-\sigma_w^{-1})\|\le Q$, for every vertex $w$. Then all these quantities are bounded by
--   $$
--   \|\operatorname{tr}_{\mathbb R}\|\,E\,\Bigl(1+\frac32L+\frac34L^2+\frac32Q\Bigr).
--   $$
--
--   Operator-norm control of the carriers and scores controls every term of the heat calculus.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/HeatBound.lean#L23-L78

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

theorem OAI.TriangularHilbert.Heat.heatAtBounds_of_norms (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    {E L Q : ℝ} (hE : 0 ≤ E) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hr : ∀ v w, ‖heatCarrier A h u p σ v w‖^3 ≤ E)
    (hl : ∀ w, ‖heatMask (fun a j => if a = w then score (u j) (p a) (σ a) else 0)‖ ≤ L)
    (hq : ∀ w, ‖heatMask (fun a j => if a = w then score (u j) (p a) (σ a)^2-(σ a)⁻¹ else 0)‖ ≤ Q) :
    HeatAtBounds A h u p σ
      (‖traceRealCLM (ι := BlockSpace ι)‖ * E * (1 + (3/2:ℝ)*L + (3/4:ℝ)*L^2 + (3/2:ℝ)*Q)) := by sorry
