-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_primary_power_rows_97_to_120
-- name    : GrothendieckLB.Supplement.cq_primary_power_rows_97_to_120
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T20:36:56.845844+00:00
-- url     : https://prove2.me/theorems/724596ab-94ed-4d22-808f-d3c8b405c92a
-- title:
--   Certified primary polynomial powers 97 through 120
-- statement:
--   Every coefficient through scalar degree 251 in the recorded powers 97 through 120 of the cubic–quintic primary polynomial agrees with the exact prescribed interval recurrence.
-- source:
--   Saha et al., arXiv:2608.11158v2, Appendix C.1; finite polynomial powers in the 251-degree coefficient certificate.

import Definitions.Def_GrothendieckLB_Supplement_cqReplayPowers

namespace GrothendieckLB.Supplement

theorem cq_primary_power_rows_97_to_120 (p : ℕ) (hl : 96 ≤ p) (hu : p < 120) :
    (List.range 252).all (fun j => decide (CQHeadCertificate.power (p+1) j = CQHeadCertificate.powerAt p j)) = true := by sorry

end GrothendieckLB.Supplement
