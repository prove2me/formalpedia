-- Prove2me | Theorems.Thm_KnodelPrimeCordial_count_selected_residue_two__p2m_26f020af_5673_4287_8efa_c1124a20bf65_a1
-- name    : KnodelPrimeCordial.count_selected_residue_two__p2m_26f020af_5673_4287_8efa_c1124a20bf65_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:36:13.627201+00:00
-- url     : https://prove2.me/theorems/55e0d80a-2c7c-4937-b944-1f9aff0b2663
-- title:
--   Count indices in residue class two
-- statement:
--   Among indices from zero through `6 * k + 2`, exactly `k + 1` are nonzero and congruent to 2 modulo 6.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib

theorem KnodelPrimeCordial.count_selected_residue_two__p2m_26f020af_5673_4287_8efa_c1124a20bf65_a1 (k : ℕ) :
    (Finset.univ.filter fun j : Fin (6 * k + 3) => j.val ≠ 0 ∧ j.val % 6 = 2).card = k + 1 := by sorry
