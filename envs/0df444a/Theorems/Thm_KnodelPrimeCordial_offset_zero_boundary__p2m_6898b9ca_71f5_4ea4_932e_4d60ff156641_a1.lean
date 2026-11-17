-- Prove2me | Theorems.Thm_KnodelPrimeCordial_offset_zero_boundary__p2m_6898b9ca_71f5_4ea4_932e_4d60ff156641_a1
-- name    : KnodelPrimeCordial.offset_zero_boundary__p2m_6898b9ca_71f5_4ea4_932e_4d60ff156641_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:34:24.726068+00:00
-- url     : https://prove2.me/theorems/59dfb6fe-b3b4-403a-a55c-2956af1446f1
-- title:
--   Handle the zero-index offset-zero pair
-- statement:
--   If n ≡ 6 modulo 12, the labels at indices 0 and n−1 are not coprime.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.offset_zero_boundary__p2m_6898b9ca_71f5_4ea4_932e_4d60ff156641_a1
    (n : ℕ) (hmod : n % 12 = 6) :
    ¬ Nat.Coprime (KnodelPrimeCordial.labelF 0)
      (KnodelPrimeCordial.labelF (n - 1)) := by sorry
