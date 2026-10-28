-- Prove2me | Theorems.Thm_OAI_OddGoldbach23_pair_quarter_0
-- name    : OAI.OddGoldbach23.pair_quarter_0
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-25T07:47:50.587582+00:00
-- url     : https://prove2.me/theorems/5aeb696f-6d49-49d0-89ff-db2e01b49709
-- title:
--   Finite sieve pair-sum certificate, rows 1–250
-- statement:
--   For rows 1 through 250 of the explicit 1000-entry list Q, the sum of the stored integer weight P(a-b) over all entries b of Q with b<a is at most 53619369. These are consecutive disjoint rows of the finite pair-sum certificate. Adding the four row-block bounds gives 867860452.
-- source:
--   Finite computational decomposition of https://prove2.me/theorems/91862081-bcf4-4bf9-8499-5e9a39e27aaf . Exact integer computation for the 1000-prime Riesel–Vaughan sieve parameter, 2026-10-25.

import Definitions.Def_OAI_OddGoldbach23_CertificateData

theorem OAI.OddGoldbach23.pair_quarter_0 : (((OAI.OddGoldbach23.Cert.Qlist.drop 0).take 250).map (fun a => (OAI.OddGoldbach23.Cert.Qlist.map (fun b => if b < a then OAI.OddGoldbach23.Cert.WP (a-b) else 0)).sum)).sum ≤ 53619369 := by sorry
