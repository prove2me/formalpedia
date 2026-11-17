-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_2_count__p2m_0097d18c_892d_47ab_91e0_b6172f62f5ff_a1
-- name    : KnodelPrimeCordial.case_mod_6_offset_2_count__p2m_0097d18c_892d_47ab_91e0_b6172f62f5ff_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:17:02.204711+00:00
-- url     : https://prove2.me/theorems/7532f8d4-700d-4daa-ba77-23877d6e6e87
-- title:
--   Coprime index count for offset 2 in residue class 6
-- statement:
--   For the third offset, exactly `(n + 2) / 4` indices have coprime endpoint labels. Prove it by the six index residue classes modulo 6, separately accounting for the inner modulo wrap and then counting the offset-specific coprimality cases.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF
open scoped BigOperators

theorem KnodelPrimeCordial.case_mod_6_offset_2_count__p2m_0097d18c_892d_47ab_91e0_b6172f62f5ff_a1
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    (Finset.univ.filter fun j : Fin (n / 2) =>
      Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card =
      (n + 2) / 4 := by sorry
