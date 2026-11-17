-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_0_residue_count__p2m_8f071b5d_2675_41bd_8723_304b8e6b90ee_a1
-- name    : KnodelPrimeCordial.case_mod_6_offset_0_residue_count__p2m_8f071b5d_2675_41bd_8723_304b8e6b90ee_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:26:39.834429+00:00
-- url     : https://prove2.me/theorems/26f020af-5673-4287-8efa-c1124a20bf65
-- title:
--   Count positive indices in the coprime residue classes
-- statement:
--   When `n % 12 = 6`, exactly `(n + 2) / 4` indices in `Fin (n / 2)` are positive and congruent to 1, 2, or 4 modulo 6.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib

theorem KnodelPrimeCordial.case_mod_6_offset_0_residue_count__p2m_8f071b5d_2675_41bd_8723_304b8e6b90ee_a1 (n : ℕ) (hmod : n % 12 = 6) :
    (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val ≠ 0 ∧ j.val % 6 ∈ ({1, 2, 4} : Finset ℕ)).card =
      (n + 2) / 4 := by sorry
