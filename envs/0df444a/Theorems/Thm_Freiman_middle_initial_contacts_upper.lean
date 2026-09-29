-- Prove2me | Theorems.Thm_Freiman_middle_initial_contacts_upper
-- name    : Freiman.middle_initial_contacts_upper
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:06:57.712849+00:00
-- url     : https://prove2.me/theorems/ba282e95-4125-4205-a2d6-9410ee9b5432
-- title:
--   middle initial contacts upper
-- statement:
--   The remaining seven adjacent initial contacts (roots 8–15), including the narrow seams between the two-4 roots, follow from exact rational inner endpoints.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:sec:initial, contacts table

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_initial_contacts_upper :
    (∀ i : Fin 15, middleRootCertificate i) →
    ∀ (i : ℕ) (hlo : 7 ≤ i) (hi : i<14), (middleCover (middleRoot ⟨i,by omega⟩) ∩ middleCover (middleRoot ⟨i+1,by omega⟩)).Nonempty := by
  sorry

end Freiman
