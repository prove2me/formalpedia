-- Prove2me | Theorems.Thm_KnodelPrimeCordial_knodel_three_regular_side1_residue_card__p2m_165d50bc_4001_44b9_bb11_e1f7ef0e1992_a1
-- name    : KnodelPrimeCordial_knodel_three_regular_side1_residue_card__p2m_165d50bc_4001_44b9_bb11_e1f7ef0e1992_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:38:09.164423+00:00
-- url     : https://prove2.me/theorems/a8c8f21b-ebf8-4eed-9c8b-a042d060483d
-- title:
--   Distinctness of the three modular residues
-- statement:
--   For m ≥ 5 and j : Fin m, the residues j, j−1 modulo m, and j−3 modulo m are pairwise distinct, so their Finset has cardinality three.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib

theorem KnodelPrimeCordial_knodel_three_regular_side1_residue_card__p2m_165d50bc_4001_44b9_bb11_e1f7ef0e1992_a1 (m : ℕ) (hm : 5 ≤ m) (j : Fin m) : ({j.val, (j.val + m - 1) % m, (j.val + m - 3) % m} : Finset ℕ).card = 3 := by sorry
