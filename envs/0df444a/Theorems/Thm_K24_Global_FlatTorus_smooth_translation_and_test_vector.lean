-- Prove2me | Theorems.Thm_K24_Global_FlatTorus_smooth_translation_and_test_vector
-- name    : K24.Global.FlatTorus.smooth_translation_and_test_vector
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T19:08:24.493811+00:00
-- url     : https://prove2.me/theorems/2ab66550-ac20-4562-b5b6-bfa2f55410be
-- title:
--   K24: smooth quotient torus, invariant circle translation and zero-average test vector
-- statement:
--   The exact four-torus Torus = Fin 4 → Circle with the original quotient-map charted structure is a smooth real four-manifold. There exists an original CircleAction Torus whose action is exactly translate, rotating the second factor, such that the original flatMetric is invariant under this action, the original testVector is Haar-integrable in every canonical coordinate chart, and its original normalized Haar projection vectorPi0 is zero (the exact original IsNonzeroVector predicate). These are the literal geometric and Haar clauses of FlatTorus.SharpnessStatement, independent of the Holder exponent. The atlas, covering map, manifold differential, frame, coframe, metric, action and test vector are all the unchanged official definitions. The remaining Holder norm finiteness, uniform estimates, convergence, positive lower bound and vector-operator identity are separate obligations; this theorem does not assert full sharpness or FullK24Statement.
-- source:
--   Child dependency of original theorem aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22, FullK24Statement fourth conjunct FlatTorus.SharpnessStatement. It proves the unchanged smooth-manifold, prescribed-action, flat-metric-invariance, test-vector Haar-integrability and zero-average clauses in official definition node 9140e2e8-3049-4225-86fe-cfe1a8c49825. Original source K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md, commit 8c02be189f097080feca952347c9104bfb986242; original definitions and root type remain unchanged.

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
open scoped Manifold ContDiff

namespace K24.Global.FlatTorus
theorem smooth_translation_and_test_vector :
  IsManifold I4 ∞ Torus ∧
    ∃ rho : CircleAction Torus,
      rho.act = translate ∧ IsInvariantCov2 rho flatMetric ∧
      VectorHaarIntegrable rho testVector ∧ IsNonzeroVector rho testVector := by
  sorry
end K24.Global.FlatTorus
