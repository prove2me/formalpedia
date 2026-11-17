-- Prove2me | Theorems.Thm_KnodelPrimeCordial_offset_zero_index_wrap__p2m_6898b9ca_71f5_4ea4_932e_4d60ff156641_a1
-- name    : KnodelPrimeCordial.offset_zero_index_wrap__p2m_6898b9ca_71f5_4ea4_932e_4d60ff156641_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:34:16.572443+00:00
-- url     : https://prove2.me/theorems/664c17d9-919c-412e-9775-a21419958b1a
-- title:
--   Reduce the nonzero offset-zero index modulo the cycle length
-- statement:
--   Under n ≡ 6 modulo 12, the target’s wrapped index equals 2j−1 for every nonzero j in Fin (n / 2).
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib

theorem KnodelPrimeCordial.offset_zero_index_wrap__p2m_6898b9ca_71f5_4ea4_932e_4d60ff156641_a1
    (n : ℕ) (hmod : n % 12 = 6) (j : Fin (n / 2)) (hj : j.val ≠ 0) :
    (2 * ((j.val + 2 ^ 0 - 1) % (n / 2)) + n - 1) % n =
      2 * j.val - 1 := by sorry
