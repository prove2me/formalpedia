-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_windowTrace_eq
-- name    : OAI.TriangularHilbert.Heat.windowTrace_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:59:56.73658+00:00
-- url     : https://prove2.me/theorems/357f8977-f16a-4788-82af-6d2348cec607
-- title:
--   Expansion of the window trace as a cyclic sum
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. The odd window is $\omega_s(t)=\frac{t}{\sqrt s}\phi_s(t)$ and the signed kernel is $\kappa_s(t)=\frac{t^3/27-ts/3}{s\sqrt s}\phi_{3s}(t)$, with $\phi_\sigma$ the centred Gaussian density of variance $\sigma$. For $h,s>0$, the window trace with heat arrays of variance $\frac{11}{10}s$ and window diagonals $\omega_s/\phi_{11s/10}$ equals
--   $$
--   \mathrm{windowTrace}=\sum_{i,j,k}h^3A_0(i,j)\,A_1(j,k)\,A_2(k,i)\;\omega_s(u_i-p_0)\,\omega_s(u_j-p_1)\,\omega_s(u_k-p_2).
--   $$
--
--   The trace is the cyclic trilinear form with odd windows centred at the three heat centres.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/SignedExpansion.lean#L49-L71

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uι
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.Heat.windowTrace_eq (A : Three → Matrix ι ι ℂ) {h s : ℝ} (hh : 0 < h) (hs : 0 < s)
    (u : ι → ℝ) (p : Three → ℝ) :
    windowTrace A h u p s = ∑ i, ∑ j, ∑ k,
      (h^3:ℝ)* (A 0 i j*A 1 j k*A 2 k i) *
        ((oddWindow s (u i-p 0)*oddWindow s (u j-p 1)*oddWindow s (u k-p 2):ℝ):ℂ) := by sorry
