-- Prove2me | Theorems.Thm_K24_Global_coefficient_and_vector_difference_identities
-- name    : K24.Global.coefficient_and_vector_difference_identities
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T18:46:07.003995+00:00
-- url     : https://prove2.me/theorems/67a1ef0f-2cf3-4161-a3ca-0d5439119dad
-- title:
--   K24: exact connection, Bianchi and actual-metric vector differences
-- statement:
--   Let M be a smooth real four-manifold, and let ĝ and z be positive symmetric metrics whose actual coordinate matrices are C¹. The theorem proves three identities for the unchanged canonical K24 geometric operators.
--
--   1. In every valid canonical chart target, put e=ĝ−z and D=Γ(ĝ)−Γ(z). Then
--   $$D^k_{ij}=\frac12\widehat g^{k\ell}(\nabla^z_i e_{j\ell}+\nabla^z_j e_{i\ell}-\nabla^z_\ell e_{ij}).$$
--   2. For every C¹ bilinear tensor u (symmetry of u is not required), put A=ĝ⁻¹−z⁻¹. The full Bianchi difference, with repeated indices summed, is
--   $$\begin{aligned}(\beta_{\widehat g}u-\beta_z u)_j={}&-A^{ab}\nabla^z_a u_{bj}+\tfrac12 A^{ab}\nabla^z_j u_{ab}\\&+\widehat g^{ab}D^p_{ab}u_{pj}+\widehat g^{ab}D^p_{aj}u_{bp}+\tfrac12(\nabla^z_j A^{ab})u_{ab}.\end{aligned}$$
--   The derivative of the inverse difference is retained.
--   3. For any raw tensor g and raw vector field Y for which g, L_Y g and L_Y z have the explicitly required C¹ coordinate regularity,
--   $$\beta_{\widehat g}(L_Yg)-\beta_z(L_Yz)=(\beta_{\widehat g}-\beta_z)(L_Yz)+\beta_{\widehat g}(L_Y(g-z)).$$
--   This is equality of the canonical reconstructed global covector fields. No symmetry or positivity of g, and no separate regularity assumption on Y, is added beyond the three explicit tensor regularity assumptions.
--
--   The result supplies the connection and Bianchi coefficient formulas and the unprojected two-error identity behind K24 equations (3.2), (3.4), and (5.4). It preserves arbitrary smooth four-manifolds, including the empty case, and assumes no compactness, invariance or proximity of the two metrics. The exact canonical Holder-to-chart and Lie-regularity bridges, genuine Haar-projection integrability, geometric estimates, Sobolev claims and sharpness remain obligations of the original full target https://prove2.me/theorems/aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 . This supporting theorem does not assert full K24 completion.
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — equations (3.2), (3.4), and the unprojected identity behind (5.4); canonical geometry definition 307243a3-0dec-4e35-a891-6249f62e8aee.

import Definitions.Def_K24GlobalGeometry
set_option autoImplicit false
open scoped Manifold ContDiff

namespace K24.Global
universe u
theorem coefficient_and_vector_difference_identities :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M],
    ∀ ghat z : RawCov2 M, IsMetric ghat → IsMetric z →
      Cov2ContDiff 1 ghat → Cov2ContDiff 1 z →
      (∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
        ∀ k i j : Fin 4,
          connectionDifferenceInChart ghat z c x k i j =
            connectionDifferenceExpansion ghat z c x k i j) ∧
      (∀ u : RawCov2 M, Cov2ContDiff 1 u →
        ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
          ∀ j : Fin 4, bianchiInChart ghat u c x j - bianchiInChart z u c x j =
            bianchiDifferenceExpansion ghat z u c x j) ∧
      (∀ (g : RawCov2 M) (Y : RawVector M),
        Cov2ContDiff 1 g → Cov2ContDiff 1 (lieTensor Y g) →
        Cov2ContDiff 1 (lieTensor Y z) →
        vectorOperator ghat g Y - vectorOperator z z Y =
          actualMetricVectorDefect ghat z g Y)
:= by sorry
end K24.Global
