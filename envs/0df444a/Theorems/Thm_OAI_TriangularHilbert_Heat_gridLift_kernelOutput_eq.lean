-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_gridLift_kernelOutput_eq
-- name    : OAI.TriangularHilbert.Heat.gridLift_kernelOutput_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:35:55.509282+00:00
-- url     : https://prove2.me/theorems/f92e4e10-9de5-4b60-aa72-fdddca398721
-- title:
--   Grid lift of the discrete kernel output equals the sampled output
-- statement:
--   For functions $B,C$ on the plane and a kernel $K$, the cyclic kernel output is $\int_{\mathbb R}B(z_2,c)\,C(c,z_1)\,K(z_1+z_2+c)\,dc$, and the hard kernel is $H_{r,R}(t)=\mathbf 1_{r<|t|\le R}/t$. Let $B,C$ be supported in $[-M,M]^2$, $h>0$, and let $D$ be the grid indices with $|hi|\le M$. Let $\mathrm{sampledMatrix}(F)(i,j)=F(hi,hj)$. Then for every $z$,
--   $$
--   \mathrm{gridLift}\Bigl(\sum_kh\,\mathrm{sampled}(B)_{jk}\,\mathrm{sampled}(C)_{ki}\,K(hi+hj+hk)\Bigr)(z)=\int_{\mathbb R}B(\bar z_2,\bar c)\,C(\bar c,\bar z_1)\,K(\bar z_1+\bar z_2+\bar c)\,dc,
--   $$
--   where $\bar x=h\lfloor x/h\rfloor$ is the grid point of $x$.
--
--   The discrete kernel output is the continuum output of the sampled functions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/SampledOutput.lean#L37-L57

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators

theorem OAI.TriangularHilbert.Heat.gridLift_kernelOutput_eq (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h)
    (hB : BoxSupport B M) (hC : BoxSupport C M) (K : ℝ → ℝ) (z : ℝ×ℝ) :
    gridLift (sampleIndices h M) h (kernelOutput (sampledMatrix B h M) (sampledMatrix C h M) h
      (fun m => h*(m:ℤ)) (fun _ _ => K)) z = sampledKernelOutput B C h K z := by sorry
