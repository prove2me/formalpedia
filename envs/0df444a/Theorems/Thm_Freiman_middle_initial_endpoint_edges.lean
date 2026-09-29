-- Prove2me | Theorems.Thm_Freiman_middle_initial_endpoint_edges
-- name    : Freiman.middle_initial_endpoint_edges
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:06:52.371156+00:00
-- url     : https://prove2.me/theorems/d5d989dd-4cde-4f00-a89f-1d471b6bcd63
-- title:
--   middle initial endpoint edges
-- statement:
--   The inner left endpoint of root 15 has square below 21; the inner right endpoint of root 1 exceeds 128/25. These strict outer margins ensure both target endpoints are covered.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:sec:initial, last paragraph

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_initial_endpoint_edges :
    (∀ i : Fin 15, middleRootCertificate i) →
      (middleBounds (middleRoot 14)).1 < Real.sqrt 21 ∧ (128/25:ℝ)<(middleBounds (middleRoot 0)).2 := by
  sorry

end Freiman
