-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_2_residue_0_count__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
-- name    : KnodelPrimeCordial.case_mod_6_offset_2_residue_0_count__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:31:40.756199+00:00
-- url     : https://prove2.me/theorems/43df6e99-1e39-4482-9fc2-f634faa5d9d0
-- title:
--   Offset-two coprimality count in residue class zero
-- statement:
--   Among indices congruent to zero modulo 6, no offset-two endpoint pair has coprime labels. The nonwrapped pairs are even; the final wrapped index also has even labels.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.case_mod_6_offset_2_residue_0_count__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val % 6 = 0 ∧
      Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card = 0 := by sorry
