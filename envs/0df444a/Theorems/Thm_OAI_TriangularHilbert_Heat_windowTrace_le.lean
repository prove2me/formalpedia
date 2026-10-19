-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_windowTrace_le
-- name    : OAI.TriangularHilbert.Heat.windowTrace_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:55:40.94641+00:00
-- url     : https://prove2.me/theorems/15b69265-8bb6-4a0b-9e6b-f1fd17630d05
-- title:
--   The window trace is bounded by the strict Hessian dissipation
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. The odd window is $\omega_s(t)=\frac{t}{\sqrt s}\phi_s(t)$ and the signed kernel is $\kappa_s(t)=\frac{t^3/27-ts/3}{s\sqrt s}\phi_{3s}(t)$, with $\phi_\sigma$ the centred Gaussian density of variance $\sigma$. For $h,s>0$, the window trace $\operatorname{tr}(W_0\tilde A_0W_1\tilde A_1W_2\tilde A_2)$ uses heat arrays $\tilde A$ of variance $\frac{11}{10}s$ and window diagonals $W_v=\operatorname{diag}\bigl(\omega_s/\phi_{11s/10}\bigr)$. It satisfies
--   $$
--   \bigl|\mathrm{windowTrace}\bigr|\le\frac{440}3\,s\sum_v\mathrm{heatCost}\bigl(\sigma_z=\mathrm{strictRate}(v,z)\,s\bigr)(v,v),
--   $$
--   where the strict rates are $1$ at $v$ and $\frac{11}{10}$ elsewhere.
--
--   The signed cyclic form at scale $s$ is controlled by the Hessian dissipation of the heat flow.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/SignedTraceOrder.lean#L112-L130

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uι
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.Heat.windowTrace_le (A : Three → Matrix ι ι ℂ) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s) (u : ι → ℝ) (p : Three → ℝ) :
    ‖windowTrace A h u p s‖ ≤ (440/3)*s*∑ v,
      heatCost A h u p (fun z => strictRate v z*s) v v := by sorry
