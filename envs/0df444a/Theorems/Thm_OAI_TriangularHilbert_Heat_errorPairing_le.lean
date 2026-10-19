-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_errorPairing_le
-- name    : OAI.TriangularHilbert.Heat.errorPairing_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:27:56.893167+00:00
-- url     : https://prove2.me/theorems/f11e6f49-3e94-4b8d-a3ca-49db87324c40
-- title:
--   The endpoint error pairing is bounded by the cubic mass
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. The grid is a finite set $D\subset\mathbb Z$ with positions $u_m=hm$, $\mathrm{arrayCubic}(A,h)=\sum_v\sum_{i,j}h^2|A_v(i,j)|^3$, and the discrete cyclic pairing with entry-dependent kernels $K_{ij}$ is $\sum_{i,j,k}h^3A_0(i,j)A_1(j,k)A_2(k,i)K_{ij}(u_i+u_j+u_k)$. Let $h>0$ and radii $r_{ij}\ge h$. With the endpoint error kernels $K_{ij}=\mathrm{endpointError}(r_{ij},\cdot)$, the difference between the smooth and the sharp truncation at radius $r_{ij}$, the pairing satisfies
--   $$
--   \Bigl|\sum_{i,j,k}h^3A_0(i,j)A_1(j,k)A_2(k,i)\,\mathrm{endpointError}(r_{ij},u_i+u_j+u_k)\Bigr|\le C_{\mathrm{err}}\,\mathrm{arrayCubic}(A,h).
--   $$
--
--   The errors from smoothing the truncation endpoints are harmless.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/ErrorPairing.lean#L57-L84

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators

theorem OAI.TriangularHilbert.Heat.errorPairing_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) {h : ℝ} (hh : 0 < h)
    (r : Matrix D D ℝ) (hr : ∀ i j, h ≤ r i j) :
    ‖kernelPairing A h (fun m => h*(m:ℤ)) (fun i j => endpointError (r i j))‖ ≤
      errorPairingConstant*arrayCubic A h := by sorry
