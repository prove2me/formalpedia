-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_finite_masked_dissipation
-- name    : OAI.TriangularHilbert.Heat.finite_masked_dissipation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:21:32.912467+00:00
-- url     : https://prove2.me/theorems/9c4f6923-f039-481c-83c8-12adcae852e7
-- title:
--   Dissipation bound for a piecewise constant switching of edge zero
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. The total plane energy $\mathrm{TPE}(\sigma)$ is the sum over the three vertices of the heat star energies $\operatorname{tr}(R_v^*R_v)^{3/2}$, integrated over centres $p_0+p_1+p_2=d$. Under strict rates the variances are $\sigma_w=s$ at a distinguished vertex $r$ and $\frac{11}{10}s$ at the other two, and $c_\ast=\frac12\min\bigl(1-\frac35\sqrt2,\frac{11}{10}-\frac12\sqrt2\bigr)$. The grid is a finite set $D\subset\mathbb Z$ with positions $u_m=hm$, and $\mathrm{arrayCubic}(A,h)=\sum_v\sum_{i,j}h^2|A_v(i,j)|^3$. Let $B_0,B_1,\dots$ be matrices entrywise dominated by $A_0$ with total variation $\sum_{k<n}|B_{k+1}(i,j)-B_k(i,j)|\le2|A_0(i,j)|$, and let $t_0\le t_1\le\dots$ with $t_0\ge h^2$. On $[t_k,t_{k+1}]$ use the array with edge $0$ replaced by $B_k$. Then
--   $$
--   c_\ast\sum_{k<n}\int_{t_k}^{t_{k+1}}\sum_v\mathrm{planeIntegral}\bigl(\mathrm{heatCost}(\cdot,v,v)\bigr)\,ds\le C_{\mathrm{mask}}\,\mathrm{arrayCubic}(A,h).
--   $$
--
--   Switching entries on and off costs only a bounded amount of energy in total.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/MaskedDissipation.lean#L87-L113

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
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_Switch
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedDissipation

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uι
open MatrixEnergy MeasureTheory
open scoped BigOperators

theorem OAI.TriangularHilbert.Heat.finite_masked_dissipation (D : Finset ℤ) (A : Three → Matrix D D ℂ)
    (B : ℕ → Matrix D D ℂ) (hB : ∀ k i j, ‖B k i j‖ ≤ ‖A 0 i j‖) (n : ℕ)
    (hvar : ∀ i j, (∑ k ∈ Finset.range n, ‖B (k+1) i j-B k i j‖) ≤ 2*‖A 0 i j‖)
    {h : ℝ} (hh : 0 < h) (t : ℕ → ℝ) (ht : Monotone t) (ht0 : h^2 ≤ t 0) (r : Three) :
    strictConstant * (∑ k ∈ Finset.range n,
      ∫ s in t k..t (k+1), ∑ v, planeIntegral (fun p => heatCost (replaceZero A (B k)) h
        (fun m => h*(m:ℤ)) p (fun z => strictRate r z*s) v v) 0) ≤ maskedConstant*arrayCubic A h := by sorry
