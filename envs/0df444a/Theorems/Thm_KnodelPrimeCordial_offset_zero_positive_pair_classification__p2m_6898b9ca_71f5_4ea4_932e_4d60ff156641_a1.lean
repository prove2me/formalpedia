-- Prove2me | Theorems.Thm_KnodelPrimeCordial_offset_zero_positive_pair_classification__p2m_6898b9ca_71f5_4ea4_932e_4d60ff156641_a1
-- name    : KnodelPrimeCordial.offset_zero_positive_pair_classification__p2m_6898b9ca_71f5_4ea4_932e_4d60ff156641_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:34:20.134209+00:00
-- url     : https://prove2.me/theorems/3ffbdccd-5f9f-4932-88cb-ab4d201f0b16
-- title:
--   Classify positive neighboring labels for offset zero
-- statement:
--   For every positive natural index j, the labels at 2j and 2j−1 are coprime exactly when j has residue 1, 2, or 4 modulo 6.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.offset_zero_positive_pair_classification__p2m_6898b9ca_71f5_4ea4_932e_4d60ff156641_a1 (j : ℕ) (hj : 0 < j) :
    Nat.Coprime (KnodelPrimeCordial.labelF (2 * j))
      (KnodelPrimeCordial.labelF (2 * j - 1)) ↔
    j % 6 ∈ ({1, 2, 4} : Finset ℕ) := by sorry
