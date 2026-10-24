-- Prove2me | Theorems.Thm_K24_Global_projected_actual_vector_defect_identity
-- name    : K24.Global.projected_actual_vector_defect_identity
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T18:23:48.6274+00:00
-- url     : https://prove2.me/theorems/c72d671c-8c19-43c3-b38a-0c82b7dab7ac
-- title:
--   Complete projected actual-metric vector defect with explicit regularity
-- statement:
--   This supporting lemma establishes the complete two-term projected vector comparison in K24's actual-metric refinement. Let $\rho$ be the common smooth circle action, let $\widehat g,z,g$ be covariant two-tensor sections, and let $Y$ be a vector section. Assume that $g,z,\mathcal L_Yg,\mathcal L_Yz$ have $C^1$ coefficients in every canonical chart, the inverse reference-metric coefficient matrix is differentiable on every chart target, and both $\beta_{\widehat g}\mathcal L_Yg$ and $\beta_z\mathcal L_Yz$ are fiberwise Haar integrable. Then
--   $$B_{\widehat g,g}Y-B_{z,z}Y=\Pi_\perp\!\left[(\beta_{\widehat g}-\beta_z)\mathcal L_Yz+\beta_{\widehat g}\mathcal L_Y(g-z)\right],$$
--   where $B_{h,q}Y=\Pi_\perp\beta_h\mathcal L_Yq$ and $\Pi_\perp$ uses the actual normalized Haar integral of the given action.
--
--   Both metric-error terms are retained. The statement uses the published differential and integral operators, not arbitrary maps equipped with the desired identity. The listed regularity and integrability assumptions are explicit premises of this reusable lemma. Proving them from the full K24 hypotheses, and proving the norm estimates, remain obligations of https://prove2.me/theorems/aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 .
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md; actual-metric vector refinement, retaining both errors; explicit conditional regularity formulation

import Definitions.Def_K24GlobalGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise

namespace K24.Global
universe uM

theorem projected_actual_vector_defect_identity
    {M : Type uM} [TopologicalSpace M] [ChartedSpace FourSpace M]
    (rho : CircleAction M) (ghat z g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff 1 g) (hz : Cov2ContDiff 1 z)
    (hLg : Cov2ContDiff 1 (lieTensor Y g))
    (hLz : Cov2ContDiff 1 (lieTensor Y z))
    (hinv : ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
      DifferentiableAt ℝ (inverseMetricInChart ghat c) x)
    (hfixed : CovectorHaarIntegrable rho (vectorOperator ghat g Y))
    (hcenter : CovectorHaarIntegrable rho (vectorOperator z z Y)) :
    projectedVectorOperator rho ghat g Y - projectedVectorOperator rho z z Y =
      projectedActualVectorDefect rho ghat z g Y := by
  sorry
end K24.Global
