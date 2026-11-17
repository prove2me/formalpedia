-- Prove2me | Theorems.Thm_KnodelPrimeCordial_labelF_mod_6_injOn__p2m_48a5a004_52cb_4c8e_8f15_c1802c1a70b4_a3
-- name    : KnodelPrimeCordial.labelF_mod_6_injOn__p2m_48a5a004_52cb_4c8e_8f15_c1802c1a70b4_a3
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:12:49.68099+00:00
-- url     : https://prove2.me/theorems/1c360c69-c5d8-4c8d-84a8-c6288399f80a
-- title:
--   The residue-six labeling is injective on the index interval
-- statement:
--   Equal labels of two indices in the stated interval imply that the indices are equal. Decompose both indices into block quotient and residue; the twelve offsets are a permutation, and the final partial block has six distinct offsets in its own label block.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.labelF_mod_6_injOn__p2m_48a5a004_52cb_4c8e_8f15_c1802c1a70b4_a3 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    Set.InjOn KnodelPrimeCordial.labelF (Set.Icc 0 (n - 1)) := by sorry
