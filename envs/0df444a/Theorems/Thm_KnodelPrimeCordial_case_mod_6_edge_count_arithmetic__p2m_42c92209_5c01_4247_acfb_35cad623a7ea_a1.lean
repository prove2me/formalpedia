-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_6_edge_count_arithmetic__p2m_42c92209_5c01_4247_acfb_35cad623a7ea_a1
-- name    : KnodelPrimeCordial.case_mod_6_edge_count_arithmetic__p2m_42c92209_5c01_4247_acfb_35cad623a7ea_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:03:17.972187+00:00
-- url     : https://prove2.me/theorems/09d5ad41-d63b-42b2-b02b-457801360f54
-- title:
--   Evaluate the residue-six coprimality sums
-- statement:
--   Evaluate the three index sums using the residue cases of `labelF`, including cyclic wraparound, to obtain `(3*n+2)/4`.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF
open scoped BigOperators

theorem KnodelPrimeCordial.case_mod_6_edge_count_arithmetic__p2m_42c92209_5c01_4247_acfb_35cad623a7ea_a1
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    ∑ k : Fin 3,
      (Finset.univ.filter fun j : Fin (n / 2) =>
        Nat.Coprime
          (KnodelPrimeCordial.labelF (2 * j.val))
          (KnodelPrimeCordial.labelF
            ((2 * ((j.val + 2 ^ k.val - 1) % (n / 2)) + n - 1) % n))).card =
      (3 * n + 2) / 4 := by sorry
