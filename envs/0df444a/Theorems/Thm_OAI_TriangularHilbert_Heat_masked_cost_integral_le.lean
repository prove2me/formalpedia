-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_masked_cost_integral_le
-- name    : OAI.TriangularHilbert.Heat.masked_cost_integral_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:25:55.328002+00:00
-- url     : https://prove2.me/theorems/9ff15b29-4f73-4d37-9106-7127e3cfa9a8
-- title:
--   Integrated Hessian cost of entrywise windowed arrays
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. The total plane energy $\mathrm{TPE}(\sigma)$ is the sum over the three vertices of the heat star energies $\operatorname{tr}(R_v^*R_v)^{3/2}$, integrated over centres $p_0+p_1+p_2=d$. Under strict rates the variances are $\sigma_w=s$ at a distinguished vertex $r$ and $\frac{11}{10}s$ at the other two, and $c_\ast=\frac12\min\bigl(1-\frac35\sqrt2,\frac{11}{10}-\frac12\sqrt2\bigr)$. The grid is a finite set $D\subset\mathbb Z$ with positions $u_m=hm$, and $\mathrm{arrayCubic}(A,h)=\sum_v\sum_{i,j}h^2|A_v(i,j)|^3$. Let each entry $(i,j)$ of edge $0$ carry a scale window $[a_{ij},b_{ij})$ with endpoints in a nonempty finite set $S$ of times, all at least $h^2$. Let $\mathrm{maskedCost}(s)$ be the Hessian dissipation of the array whose edge $0$ keeps only the entries active at time $s$. Then for every distinguished vertex $r$,
--   $$
--   c_\ast\int_{\min S}^{\max S}\mathrm{maskedCost}(s)\,ds\le C_{\mathrm{mask}}\,\mathrm{arrayCubic}(A,h).
--   $$
--
--   Entry-dependent truncation windows are paid for by the cubic mass.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/MaskedActual.lean#L52-L78

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
import Definitions.Def_OAI_Analysis_TriangularHilbert_SortedWindows
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedActual

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uι
open MatrixEnergy MeasureTheory
open scoped BigOperators
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.Heat.masked_cost_integral_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) (a b : Matrix D D ℝ)
    (hab : ∀ i j, a i j ≤ b i j) (S : Finset ℝ) (hS : S.Nonempty)
    (ha : ∀ i j, a i j ∈ S) (hb : ∀ i j, b i j ∈ S)
    {h : ℝ} (hh : 0 < h) (hl : ∀ s ∈ S, h^2 ≤ s) (r : Three) :
    strictConstant*(∫ s in S.min' hS..S.max' hS, maskedCost A a b h (fun m => h*(m:ℤ)) r s) ≤
      maskedConstant*arrayCubic A h := by sorry
