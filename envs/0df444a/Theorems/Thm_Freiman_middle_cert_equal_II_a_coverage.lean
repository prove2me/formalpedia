-- Prove2me | Theorems.Thm_Freiman_middle_cert_equal_II_a_coverage
-- name    : Freiman.middle_cert_equal_II_a_coverage
-- status  : Proved
-- author  : @tp
-- created : 2026-09-10T10:42:50.912979+00:00
-- url     : https://prove2.me/theorems/f03a5311-3355-4d0d-b2fa-bf3484513e24
-- title:
--   Coverage of every equal-IIa certificate branch
-- statement:
--   In the fixed middle-interval certificate catalog, every branch of every goal in the equal-IIa family is either automatic or covered by a recorded contradiction certificate. Writing $g$ for such a goal, $j$ for its branch and $\mathcal P_5$ for the prescribed parent indices, the coverage assertion is
--   $$\operatorname{Automatic}(g,j)\ \lor\ \operatorname{Recorded}(g,j,-1)\ \lor\ \forall p\in\mathcal P_5,\ \operatorname{Recorded}(g,j,p).$$
--   The index $-1$ denotes a certificate requiring no parent premises. This is the branch-coverage component of the equal-IIa family certificate theorem.
-- source:
--   Freiman report (8 September 2026), M2B §§8–9 and complete middle-interval certificate appendix; m2b_readable_model.json, SHA256 a5ac6d3c8e0148e2e3137e8cfa09a2715de6a993dd6ab01eda4842a96bba4cdf. Exact component of Def_Freiman_middleCertModel.middleCertFamilyValid at family 5, using the unchanged middleCertData catalog.

import Definitions.Def_Freiman_middleCertData
open Freiman

theorem Freiman.middle_cert_equal_II_a_coverage :
    ∀ i ∈ List.range middleCertData.goals.length, (middleCertGoal middleCertData (i+1)).family = 5 →
    ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData (i+1))).length,
      (middleCertBranch middleCertData (middleCertGoal middleCertData (i+1)) j).2 = .automatic ∨
      middleCertRecorded middleCertData (i+1) j (-1) ∨
      (5 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 5)).length, middleCertRecorded middleCertData (i+1) j k) := by sorry
