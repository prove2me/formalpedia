-- Prove2me | Theorems.Thm_KnodelPrimeCordial_labelF_mod_6_bijective__p2m_9ac481dd_4e35_42fc_b8a2_93d77d603321_a2
-- name    : KnodelPrimeCordial.labelF_mod_6_bijective__p2m_9ac481dd_4e35_42fc_b8a2_93d77d603321_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T10:29:31.59461+00:00
-- url     : https://prove2.me/theorems/48a5a004-52cb-4c8e-8f15-c1802c1a70b4
-- title:
--   The residue-six labeling permutes the label interval
-- statement:
--   For the target hypotheses, the defined `labelF` bijects indices `0,…,n−1` with labels `1,…,n`. Complete blocks of twelve map to permutations of their label blocks; the final six indices map to the final six labels.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.labelF_mod_6_bijective__p2m_9ac481dd_4e35_42fc_b8a2_93d77d603321_a2 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    Set.BijOn KnodelPrimeCordial.labelF (Set.Icc 0 (n - 1)) (Set.Icc 1 n) := by sorry
