-- Prove2me | Theorems.Thm_KnodelPrimeCordial_labelF_mod_6_surjOn__p2m_48a5a004_52cb_4c8e_8f15_c1802c1a70b4_a3
-- name    : KnodelPrimeCordial.labelF_mod_6_surjOn__p2m_48a5a004_52cb_4c8e_8f15_c1802c1a70b4_a3
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:12:50.048077+00:00
-- url     : https://prove2.me/theorems/d0c4e38d-a74d-4dce-be34-52472cbb3ecd
-- title:
--   The residue-six labeling covers the label interval
-- statement:
--   Every label in the stated interval has a preimage among the stated indices. Invert the twelve-residue offset table in each complete block; for the final six labels, use residues 3, 0, 4, 1, 2, 5 for offsets 1 through 6, respectively.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.labelF_mod_6_surjOn__p2m_48a5a004_52cb_4c8e_8f15_c1802c1a70b4_a3 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    Set.SurjOn KnodelPrimeCordial.labelF (Set.Icc 0 (n - 1)) (Set.Icc 1 n) := by sorry
