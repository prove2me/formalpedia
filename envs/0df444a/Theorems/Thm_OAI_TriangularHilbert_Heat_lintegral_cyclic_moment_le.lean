-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_lintegral_cyclic_moment_le
-- name    : OAI.TriangularHilbert.Heat.lintegral_cyclic_moment_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:52:37.466113+00:00
-- url     : https://prove2.me/theorems/41705f3e-9134-497d-adc2-d00b31f5a6f8
-- title:
--   Moment bound for finitely many truncations of the cyclic output
-- statement:
--   For functions $B,C$ on the plane and a kernel $K$, the cyclic kernel output is $\int_{\mathbb R}B(z_2,c)\,C(c,z_1)\,K(z_1+z_2+c)\,dc$, and the hard kernel is $H_{r,R}(t)=\mathbf 1_{r<|t|\le R}/t$. Let $B,C\in L^3(\mathbb R^2)$ and let $0<r_k\le R_k$ be finitely many truncations. Then
--   $$
--   \int_{\mathbb R^2}\max_k\Bigl|\int B(z_2,c)\,C(c,z_1)\,H_{r_k,R_k}(z_1+z_2+c)\,dc\Bigr|^{3/2}dz\le C_{\mathrm{mom}}\Bigl(\int|B|^3+\int|C|^3\Bigr),
--   $$
--   with $C_{\mathrm{mom}}=4C_{\mathrm{hard}}(C_{\mathrm{hard}}+1)$.
--
--   This is the main estimate for a finite family of truncations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/CyclicDensity.lean#L24-L45

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
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteMoment
import Definitions.Def_OAI_Analysis_TriangularHilbert_SampledMoment
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteDual
import Definitions.Def_OAI_Analysis_TriangularHilbert_DiscreteMax

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uκ
open MeasureTheory Filter
open scoped Topology ENNReal

theorem OAI.TriangularHilbert.Heat.lintegral_cyclic_moment_le (B C : ℝ×ℝ → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (r R : κ → ℝ) (hr : ∀ k, 0 < r k) (hR : ∀ k, r k ≤ R k) :
    (∫⁻ z : ℝ×ℝ, ENNReal.ofReal (finiteMoment (fun k => cyclicKernelOutput B C (hardKernel (r k) (R k)) z))) ≤
      ENNReal.ofReal (momentConstant*((∫ z : ℝ×ℝ, ‖B z‖^3)+(∫ z : ℝ×ℝ, ‖C z‖^3))) := by sorry
