-- Prove2me | Theorems.Thm_Freiman_middle_initial_roots_1
-- name    : Freiman.middle_initial_roots_1
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:06:51.682721+00:00
-- url     : https://prove2.me/theorems/2b39ddef-1ad5-453b-8f6e-95f1cfcbbb20
-- title:
--   middle initial roots 1
-- statement:
--   Exact regularity, strict width ratio<19/5 and rational inner endpoint bounds for roots 1–5. The roots are the physical p.51 cores converted to outward left-word order; all constants are exact rationals.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:sec:initial, roots table rows 1–5

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_initial_roots_1 :
    ∀ i : Fin 15, 0 ≤ i.val → i.val<5 → middleRootCertificate i := by
  sorry

end Freiman
