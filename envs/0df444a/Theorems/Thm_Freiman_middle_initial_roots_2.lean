-- Prove2me | Theorems.Thm_Freiman_middle_initial_roots_2
-- name    : Freiman.middle_initial_roots_2
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:06:46.166439+00:00
-- url     : https://prove2.me/theorems/521dfcd8-8ddc-460f-93e5-79dc4ff7ebbd
-- title:
--   middle initial roots 2
-- statement:
--   Exact regularity, strict width ratio<19/5 and rational inner endpoint bounds for roots 6–10. The roots are the physical p.51 cores converted to outward left-word order; all constants are exact rationals.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:sec:initial, roots table rows 6–10

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_initial_roots_2 :
    ∀ i : Fin 15, 5 ≤ i.val → i.val<10 → middleRootCertificate i := by
  sorry

end Freiman
