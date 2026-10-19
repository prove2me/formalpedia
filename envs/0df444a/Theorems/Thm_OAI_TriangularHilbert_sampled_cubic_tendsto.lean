-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_sampled_cubic_tendsto
-- name    : OAI.TriangularHilbert.sampled_cubic_tendsto
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:35:00.201988+00:00
-- url     : https://prove2.me/theorems/5cc17f1c-e63c-4e5d-81fc-a4b31e9fd8bc
-- title:
--   Cubic norms of grid samplings converge
-- statement:
--   Let $f$ be continuous on the plane, bounded by $C$ and supported in $[-M,M]^2$. Let $h_n\in(0,1]$ with $h_n\to0$, and let $\mathrm{gridSquare}(h,z)=(h\lfloor z_1/h\rfloor,h\lfloor z_2/h\rfloor)$. Then
--   $$
--   \int_{\mathbb R^2}\bigl|f(\mathrm{gridSquare}(h_n,z))\bigr|^3dz\longrightarrow\int_{\mathbb R^2}|f(z)|^3dz .
--   $$
--
--   The discrete $L^3$ masses of grid samplings converge to the $L^3$ norm.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/BoundedBox.lean#L32-L52

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

open OAI OAI.TriangularHilbert
universe uE
open MeasureTheory Filter
open scoped Topology

theorem OAI.TriangularHilbert.sampled_cubic_tendsto (f : ℝ×ℝ → ℂ) (hf : Continuous f) {M C : ℝ}
    (hs : BoxSupport f M) (hC : 0 ≤ C) (hb : ∀ z, ‖f z‖ ≤ C)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh1 : ∀ n, h n ≤ 1) (ht : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z : ℝ×ℝ, ‖f (gridSquare (h n) z)‖^3) atTop (𝓝 (∫ z : ℝ×ℝ, ‖f z‖^3)) := by sorry
