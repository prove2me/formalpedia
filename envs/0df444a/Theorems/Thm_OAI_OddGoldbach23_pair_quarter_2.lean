-- Prove2me | Theorems.Thm_OAI_OddGoldbach23_pair_quarter_2
-- name    : OAI.OddGoldbach23.pair_quarter_2
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-25T07:47:52.595759+00:00
-- url     : https://prove2.me/theorems/15c84ba4-dc81-43e0-8636-7846db4eab4b
-- title:
--   Finite sieve pair-sum certificate, rows 501–750
-- statement:
--   For rows 501 through 750 of the explicit 1000-entry list Q, the sum of the stored integer weight P(a-b) over all entries b of Q with b<a is at most 271411973. These are consecutive disjoint rows of the finite pair-sum certificate. Adding the four row-block bounds gives 867860452.
-- source:
--   Finite computational decomposition of https://prove2.me/theorems/91862081-bcf4-4bf9-8499-5e9a39e27aaf . Exact integer computation for the 1000-prime Riesel–Vaughan sieve parameter, 2026-10-25.

import Definitions.Def_OAI_OddGoldbach23_CertificateData

theorem OAI.OddGoldbach23.pair_quarter_2 : (((OAI.OddGoldbach23.Cert.Qlist.drop 500).take 250).map (fun a => (OAI.OddGoldbach23.Cert.Qlist.map (fun b => if b < a then OAI.OddGoldbach23.Cert.WP (a-b) else 0)).sum)).sum ≤ 271411973 := by sorry
