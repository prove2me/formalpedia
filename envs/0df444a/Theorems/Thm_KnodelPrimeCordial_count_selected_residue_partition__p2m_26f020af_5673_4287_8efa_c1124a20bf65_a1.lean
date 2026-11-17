-- Prove2me | Theorems.Thm_KnodelPrimeCordial_count_selected_residue_partition__p2m_26f020af_5673_4287_8efa_c1124a20bf65_a1
-- name    : KnodelPrimeCordial.count_selected_residue_partition__p2m_26f020af_5673_4287_8efa_c1124a20bf65_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:36:16.053606+00:00
-- url     : https://prove2.me/theorems/05b3a9b6-3e83-4e8c-a8df-8240b1fd667b
-- title:
--   Partition the selected indices by residue
-- statement:
--   The selected indices split into the pairwise disjoint classes congruent to 1, 2, and 4 modulo 6.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib

theorem KnodelPrimeCordial.count_selected_residue_partition__p2m_26f020af_5673_4287_8efa_c1124a20bf65_a1 (k : ℕ) :
    (Finset.univ.filter fun j : Fin (6 * k + 3) =>
      j.val ≠ 0 ∧ j.val % 6 ∈ ({1, 2, 4} : Finset ℕ)).card =
      (Finset.univ.filter fun j : Fin (6 * k + 3) => j.val ≠ 0 ∧ j.val % 6 = 1).card +
        (Finset.univ.filter fun j : Fin (6 * k + 3) => j.val ≠ 0 ∧ j.val % 6 = 2).card +
        (Finset.univ.filter fun j : Fin (6 * k + 3) => j.val ≠ 0 ∧ j.val % 6 = 4).card := by sorry
