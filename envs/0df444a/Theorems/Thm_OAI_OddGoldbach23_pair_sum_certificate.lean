-- Prove2me | Theorems.Thm_OAI_OddGoldbach23_pair_sum_certificate
-- name    : OAI.OddGoldbach23.pair_sum_certificate
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-25T07:39:25.83897+00:00
-- url     : https://prove2.me/theorems/91862081-bcf4-4bf9-8499-5e9a39e27aaf
-- title:
--   Certified sum of the 1000-prime table weights
-- statement:
--   For the explicit list Qlist of 1000 shifts in the certificate data, the sum of WP(a-b) over entries a and b with b<a is at most 867860452. This is an exact integer computation. Together with the separate table-soundness theorem and the verified prime-list properties, it yields the finite sieve bound 867861.
-- source:
--   Explicit data for OAI.OddGoldbach23.finite_sieve_certificate, https://prove2.me/theorems/13091c6f-2fef-4cbe-b70a-0a3e74bf6cfd . Generated from exact rational prime-factor products on 2026-10-25.

import Definitions.Def_OAI_OddGoldbach23_CertificateData

theorem OAI.OddGoldbach23.pair_sum_certificate :
    (OAI.OddGoldbach23.Cert.Qlist.map (fun a => (OAI.OddGoldbach23.Cert.Qlist.map (fun b => if b < a then OAI.OddGoldbach23.Cert.WP (a-b) else 0)).sum)).sum ≤ 867860452 := by sorry
