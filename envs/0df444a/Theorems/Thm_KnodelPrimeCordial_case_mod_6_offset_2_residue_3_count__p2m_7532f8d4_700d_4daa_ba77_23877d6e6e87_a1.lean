-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_2_residue_3_count__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
-- name    : KnodelPrimeCordial.case_mod_6_offset_2_residue_3_count__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:31:46.89901+00:00
-- url     : https://prove2.me/theorems/7d06090a-0333-47b7-b8b0-067b4ac10abb
-- title:
--   Offset-two coprimality count in residue class three
-- statement:
--   Every index in residue class three is nonwrapped, and the two resulting endpoint labels are even, so this class contributes zero.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.case_mod_6_offset_2_residue_3_count__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val % 6 = 3 ∧
      Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card = 0 := by sorry
