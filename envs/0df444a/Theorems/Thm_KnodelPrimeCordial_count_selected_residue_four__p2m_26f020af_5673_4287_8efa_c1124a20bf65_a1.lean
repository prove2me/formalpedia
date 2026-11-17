-- Prove2me | Theorems.Thm_KnodelPrimeCordial_count_selected_residue_four__p2m_26f020af_5673_4287_8efa_c1124a20bf65_a1
-- name    : KnodelPrimeCordial.count_selected_residue_four__p2m_26f020af_5673_4287_8efa_c1124a20bf65_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:36:15.313208+00:00
-- url     : https://prove2.me/theorems/8e0a4f4d-8dcc-48de-b5ed-2843646bfcc5
-- title:
--   Count indices in residue class four
-- statement:
--   Among indices from zero through `6 * k + 2`, exactly `k` are nonzero and congruent to 4 modulo 6.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib

theorem KnodelPrimeCordial.count_selected_residue_four__p2m_26f020af_5673_4287_8efa_c1124a20bf65_a1 (k : ℕ) :
    (Finset.univ.filter fun j : Fin (6 * k + 3) => j.val ≠ 0 ∧ j.val % 6 = 4).card = k := by sorry
