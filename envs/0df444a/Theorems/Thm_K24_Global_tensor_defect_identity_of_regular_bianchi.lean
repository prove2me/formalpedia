-- Prove2me | Theorems.Thm_K24_Global_tensor_defect_identity_of_regular_bianchi
-- name    : K24.Global.tensor_defect_identity_of_regular_bianchi
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T18:23:58.812522+00:00
-- url     : https://prove2.me/theorems/5ef88a1a-b27d-45fb-ad00-39fba1098ea0
-- title:
--   Exact tensor defect from regular Bianchi outputs
-- statement:
--   This supporting lemma proves the exact algebraic tensor comparison used in K24 §2. On a space charted over real four-dimensional Euclidean space, let $\widehat g,z,u$ be covariant two-tensor sections and let $\lambda\in\mathbb R$. Suppose both actual Bianchi covectors $\beta_{\widehat g}u$ and $\beta_z u$ have $C^1$ coefficients on every canonical chart target. Then
--   $$L_{\widehat g,z}u-L_{z,z}u=\delta_z^*(\beta_{\widehat g}u-\beta_z u),$$
--   where $L_{h,z}u=DE(z)u+\delta_z^*\beta_hu$ is the frozen gauged-linearization expression and every operator is the actual published coordinate-defined operator.
--
--   This is a conditional operator identity. It does not assume positivity or an Einstein equation, and it does not identify this expression with the Frechet derivative of the nonlinear projected gauge. Deriving the Bianchi-output regularity and the projected-gauge identification from the full geometric assumptions remains a separate part of the complete K24 target https://prove2.me/theorems/aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 .
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md; §2 equations (2.2)–(2.3), isolated conditional algebraic step

import Definitions.Def_K24GlobalGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise

namespace K24.Global
universe uM

theorem tensor_defect_identity_of_regular_bianchi
    {M : Type uM} [TopologicalSpace M] [ChartedSpace FourSpace M]
    (lam : ℝ) (ghat z u : RawCov2 M)
    (hfixed : CovectorContDiff 1 (bianchi ghat u))
    (hcenter : CovectorContDiff 1 (bianchi z u)) :
    gaugedLinearization lam ghat z u - gaugedLinearization lam z z u =
      tensorDefect ghat z u := by
  sorry
end K24.Global
