-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_tendsto_cyclicKernelOutput_of_cubic_dom
-- name    : OAI.TriangularHilbert.Heat.tendsto_cyclicKernelOutput_of_cubic_dom
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:39:26.879111+00:00
-- url     : https://prove2.me/theorems/32a2b574-a897-42cd-bc6b-c5e29745109f
-- title:
--   Convergence of cyclic outputs under cubic domination
-- statement:
--   For functions $B,C$ on the plane and a kernel $K$, the cyclic kernel output is $\int_{\mathbb R}B(z_2,c)\,C(c,z_1)\,K(z_1+z_2+c)\,dc$, and the hard kernel is $H_{r,R}(t)=\mathbf 1_{r<|t|\le R}/t$. Let $F_n\to B$ and $G_n\to C$ almost everywhere on the plane, with $F_n,G_n$ continuous and $|F_n|^3\le D$, $|G_n|^3\le E$ for integrable $D,E$. Then for almost every $z$, simultaneously for all truncations $0<r\le R$,
--   $$
--   \int F_n(z_2,c)G_n(c,z_1)H_{r,R}(z_1+z_2+c)\,dc\longrightarrow\int B(z_2,c)C(c,z_1)H_{r,R}(z_1+z_2+c)\,dc .
--   $$
--
--   Truncated cyclic outputs pass to the limit along cubically dominated approximations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/CyclicSlice.lean#L49-L76

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology

theorem OAI.TriangularHilbert.Heat.tendsto_cyclicKernelOutput_of_cubic_dom (B C : ℝ×ℝ → ℂ) (F G : ℕ → ℝ×ℝ → ℂ)
    (hF : ∀ n, Continuous (F n)) (hG : ∀ n, Continuous (G n))
    {D E : ℝ×ℝ → ℝ} (hD : Integrable D) (hE : Integrable E)
    (hb : ∀ᵐ z : ℝ×ℝ, (∀ n, ‖F n z‖^3 ≤ D z) ∧ Tendsto (fun n => F n z) atTop (𝓝 (B z)))
    (hc : ∀ᵐ z : ℝ×ℝ, (∀ n, ‖G n z‖^3 ≤ E z) ∧ Tendsto (fun n => G n z) atTop (𝓝 (C z))) :
    ∀ᵐ z : ℝ×ℝ, ∀ r R : ℝ, 0 < r → r ≤ R →
      Tendsto (fun n => cyclicKernelOutput (F n) (G n) (hardKernel r R) z) atTop
        (𝓝 (cyclicKernelOutput B C (hardKernel r R) z)) := by sorry
