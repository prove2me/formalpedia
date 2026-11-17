-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_0_count__p2m_0097d18c_892d_47ab_91e0_b6172f62f5ff_a1
-- name    : KnodelPrimeCordial.case_mod_6_offset_0_count__p2m_0097d18c_892d_47ab_91e0_b6172f62f5ff_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:17:01.750082+00:00
-- url     : https://prove2.me/theorems/8f071b5d-2675-41bd-8723-304b8e6b90ee
-- title:
--   Coprime index count for offset 0 in residue class 6
-- statement:
--   For the first offset, exactly `(n + 2) / 4` indices have coprime endpoint labels. The inner and outer modular wraps are part of the statement. Prove it by splitting `n / 2 = 6q + 3` into six index residue classes and handling the indices that wrap at `n / 2` separately, then count the classes whose explicit label formulas give coprime values.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF
open scoped BigOperators

theorem KnodelPrimeCordial.case_mod_6_offset_0_count__p2m_0097d18c_892d_47ab_91e0_b6172f62f5ff_a1
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    (Finset.univ.filter fun j : Fin (n / 2) =>
      Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 0 - 1) % (n / 2)) + n - 1) % n))).card =
      (n + 2) / 4 := by sorry
