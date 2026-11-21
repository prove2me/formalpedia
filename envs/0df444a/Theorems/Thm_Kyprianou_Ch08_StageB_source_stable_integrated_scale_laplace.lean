-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_stable_integrated_scale_laplace
-- name    : Kyprianou.Ch08.StageB.source_stable_integrated_scale_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:37:12.642314+00:00
-- url     : https://prove2.me/theorems/ae41d8e5-e255-49ec-8923-baba901e1290
-- title:
--   Exact stable source integrated q-scale Laplace transform
-- statement:
--   For actual source-certified stable q-scale W with α>1, q>0, β>q^(1/α), the Laplace transform of integratedScale (Wq) equals 1/(β(β^α-q)). Use Proved source_stable_Phi_below_beta for the source transform domain, source HasSourceScaleFamily weighted Wq transform, and Proved Avram positive_laplace_interval_primitive_real for generic primitive integration.
-- source:
--   Kyprianou (2006) Chapter 8 Exercise 8.2(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB
theorem source_stable_integrated_scale_laplace
    (α q β : ℝ) (W : ℝ → ℝ → ℝ)
    (hα : 1 < α) (hq : 0 < q) (hβ : q ^ (1 / α) < β)
    (hW : HasSourceScaleFamily (fun v : ℝ => v ^ α) W) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-β * x) *
      integratedScale (W q) x ∂volume) =
      (β * (β ^ α - q))⁻¹ := by
  sorry
end Kyprianou.Ch08.StageB
