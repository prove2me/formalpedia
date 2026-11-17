-- Prove2me | Theorems.Thm_KnodelPrimeCordial_labelF_mod_6_mapsTo__p2m_48a5a004_52cb_4c8e_8f15_c1802c1a70b4_a3
-- name    : KnodelPrimeCordial.labelF_mod_6_mapsTo__p2m_48a5a004_52cb_4c8e_8f15_c1802c1a70b4_a3
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:12:46.7192+00:00
-- url     : https://prove2.me/theorems/057d1add-7f9b-4974-b014-23c9e7c3df04
-- title:
--   The residue-six labeling maps indices into the label interval
-- statement:
--   Every index in the stated interval maps to a label in the stated label interval. Prove this by writing n = 12*q + 6 and checking the twelve residue offsets, with the final block restricted to residues 0 through 5.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.labelF_mod_6_mapsTo__p2m_48a5a004_52cb_4c8e_8f15_c1802c1a70b4_a3 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    Set.MapsTo KnodelPrimeCordial.labelF (Set.Icc 0 (n - 1)) (Set.Icc 1 n) := by sorry
