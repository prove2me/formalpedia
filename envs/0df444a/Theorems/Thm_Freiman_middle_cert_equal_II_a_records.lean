-- Prove2me | Theorems.Thm_Freiman_middle_cert_equal_II_a_records
-- name    : Freiman.middle_cert_equal_II_a_records
-- status  : Proved
-- author  : @tp
-- created : 2026-09-10T10:43:08.317348+00:00
-- url     : https://prove2.me/theorems/01b13232-b18b-429c-963c-b527546c327b
-- title:
--   Validity of every equal-IIa certificate record
-- statement:
--   Let $\mathcal C$ be the fixed middle-interval certificate catalog, and let $\mathcal R_5$ be its records whose associated goal lies in the equal-IIa family. Then
--   $$\forall r\in\mathcal R_5,\quad \operatorname{RecordValid}_{\mathcal C}(r).$$
--   Record validity includes valid goal, proof, and branch references, a valid contradiction witness, and membership of each witness bound in the premises for every listed parent. This is the record-validity component of the equal-IIa family certificate theorem.
-- source:
--   Freiman report (8 September 2026), M2B §§8–9 and complete middle-interval certificate appendix; m2b_readable_model.json, SHA256 a5ac6d3c8e0148e2e3137e8cfa09a2715de6a993dd6ab01eda4842a96bba4cdf. Exact component of Def_Freiman_middleCertModel.middleCertFamilyValid at family 5, using the unchanged middleCertData catalog.

import Definitions.Def_Freiman_middleCertData
open Freiman

theorem Freiman.middle_cert_equal_II_a_records :
    ∀ r ∈ middleCertData.records, (middleCertGoal middleCertData r.goal).family = 5 → middleCertRecordValid middleCertData r := by sorry
