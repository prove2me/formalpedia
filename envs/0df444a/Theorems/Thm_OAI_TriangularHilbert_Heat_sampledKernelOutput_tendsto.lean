-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_sampledKernelOutput_tendsto
-- name    : OAI.TriangularHilbert.Heat.sampledKernelOutput_tendsto
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:42:03.871955+00:00
-- url     : https://prove2.me/theorems/0d3cb0c8-1a6d-4fe9-9771-75be8c19af53
-- title:
--   Sampled cyclic outputs converge for continuous box-supported functions
-- statement:
--   For functions $B,C$ on the plane and a kernel $K$, the cyclic kernel output is $\int_{\mathbb R}B(z_2,c)\,C(c,z_1)\,K(z_1+z_2+c)\,dc$, and the hard kernel is $H_{r,R}(t)=\mathbf 1_{r<|t|\le R}/t$. Let $B,C$ be continuous, bounded by $C_B,C_C$, with $B$ supported in $[-M,M]^2$. Let $K$ be measurable with $|K|\le L$ and continuous at $z_1+z_2+c$ for almost every $c$. If $h_n\in(0,1]$ and $h_n\to0$, then the sampled outputs with all coordinates rounded to the grid of mesh $h_n$ converge:
--   $$
--   \int B(\bar z_2,\bar c)\,C(\bar c,\bar z_1)\,K(\bar z_1+\bar z_2+\bar c)\,dc\longrightarrow\int B(z_2,c)\,C(c,z_1)\,K(z_1+z_2+c)\,dc .
--   $$
--
--   Discretization of the cyclic output is consistent for nice functions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/SampledConvergence.lean#L32-L56

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
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedCenter
import Definitions.Def_OAI_Analysis_TriangularHilbert_SelectedScale
import Definitions.Def_OAI_Analysis_TriangularHilbert_DiscretePairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_SmoothFormula
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorEnvelope
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_HardPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_GridCell
import Definitions.Def_OAI_Analysis_TriangularHilbert_Quantization
import Definitions.Def_OAI_Analysis_TriangularHilbert_GridLine
import Definitions.Def_OAI_Analysis_TriangularHilbert_BoundedBox
import Definitions.Def_OAI_Analysis_TriangularHilbert_SampledOutput
import Definitions.Def_OAI_Analysis_TriangularHilbert_CyclicSlice
import Definitions.Def_OAI_Analysis_TriangularHilbert_RationalSup

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology

theorem OAI.TriangularHilbert.Heat.sampledKernelOutput_tendsto (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    {M CB CC L : ℝ} (hs : BoxSupport B M) (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hL : 0 ≤ L)
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh1 : ∀ n, h n ≤ 1) (ht : Tendsto h atTop (𝓝 0))
    (K : ℝ → ℝ) (hK : Measurable K) (hk : ∀ t, |K t| ≤ L) (z : ℝ×ℝ)
    (hcont : ∀ᵐ c : ℝ, ContinuousAt K (z.1+z.2+c)) :
    Tendsto (fun n => sampledKernelOutput B C (h n) K z) atTop (𝓝 (cyclicKernelOutput B C K z)) := by sorry
