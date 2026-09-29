-- Prove2me | Theorems.Thm_Freiman_middle_initial_contacts_lower
-- name    : Freiman.middle_initial_contacts_lower
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:07:01.815253+00:00
-- url     : https://prove2.me/theorems/4057fac5-aec7-4acf-bb7f-1381563b34f1
-- title:
--   middle initial contacts lower
-- statement:
--   The first seven adjacent initial contacts (roots 1–8) follow from their displayed rational inner endpoints and exact positive overlap numerators.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:sec:initial, contacts table

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_initial_contacts_lower :
    (∀ i : Fin 15, middleRootCertificate i) →
    ∀ (i : ℕ) (hi : i<7), (middleCover (middleRoot ⟨i,by omega⟩) ∩ middleCover (middleRoot ⟨i+1,by omega⟩)).Nonempty := by
  sorry

end Freiman
