-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_2_residue_5_index_count__p2m_44d4bacb_229b_4cd5_be6a_4744e1588199_a1
-- name    : KnodelPrimeCordial.case_mod_6_offset_2_residue_5_index_count__p2m_44d4bacb_229b_4cd5_be6a_4744e1588199_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:45:51.8982+00:00
-- url     : https://prove2.me/theorems/3cfc5807-3776-4ec4-91ff-25139062df0d
-- title:
--   Count of class-five indices
-- statement:
--   Under the target hypotheses, exactly `n / 12` indices below `n / 2` have residue five modulo six.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib

theorem KnodelPrimeCordial.case_mod_6_offset_2_residue_5_index_count__p2m_44d4bacb_229b_4cd5_be6a_4744e1588199_a1
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    (Finset.univ.filter fun j : Fin (n / 2) => j.val % 6 = 5).card = n / 12 := by sorry
