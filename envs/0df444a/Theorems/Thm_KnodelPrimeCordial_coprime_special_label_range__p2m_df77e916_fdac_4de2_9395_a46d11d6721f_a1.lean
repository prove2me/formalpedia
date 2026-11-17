-- Prove2me | Theorems.Thm_KnodelPrimeCordial_coprime_special_label_range__p2m_df77e916_fdac_4de2_9395_a46d11d6721f_a1
-- name    : KnodelPrimeCordial.coprime_special_label_range__p2m_df77e916_fdac_4de2_9395_a46d11d6721f_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T10:27:21.118484+00:00
-- url     : https://prove2.me/theorems/ba874ab2-b7f2-4dc5-853d-96961ae6edbd
-- title:
--   Coprimality for special labels in the range
-- statement:
--   If `a` is `1`, `5`, or `7`, and `b` lies in `1,…,8` but differs from `a`, then their gcd is `1`. The range endpoints are included; `hne` excludes the only non-coprime equal-label cases.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.1, p.3 (PDF p.3)

import Mathlib

theorem KnodelPrimeCordial.coprime_special_label_range__p2m_df77e916_fdac_4de2_9395_a46d11d6721f_a1 {a b : ℕ} (ha : a = 1 ∨ a = 5 ∨ a = 7) (hb₁ : 1 ≤ b) (hb₈ : b ≤ 8) (hne : a ≠ b) : Nat.gcd a b = 1 := by sorry
