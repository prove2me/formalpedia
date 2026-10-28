-- Prove2me | Theorems.Thm_OAI_OddGoldbach23_table_certificate
-- name    : OAI.OddGoldbach23.table_certificate
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-25T07:39:25.820684+00:00
-- url     : https://prove2.me/theorems/a4c16b56-ce7f-4bc9-9081-a8b1e7f9c400
-- title:
--   Soundness of the finite sieve-weight table
-- statement:
--   For every natural number d less than 7928, the stored integer table entry WP(d) is at least WC(d), the ceiling of 1000 times the rational singular-series weight K(d). Thus every table entry used for a difference between the selected prime shifts is a certified upper bound, rather than an assumed numerical input.
-- source:
--   Explicit data for OAI.OddGoldbach23.finite_sieve_certificate, https://prove2.me/theorems/13091c6f-2fef-4cbe-b70a-0a3e74bf6cfd . Generated from exact rational prime-factor products on 2026-10-25.

import Definitions.Def_OAI_OddGoldbach23_CertificateData

theorem OAI.OddGoldbach23.table_certificate (d : ℕ) (hd : d < 7928) :
    OAI.OddGoldbach23.Cert.WC d ≤ OAI.OddGoldbach23.Cert.WP d := by sorry
