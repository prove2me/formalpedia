-- Prove2me | Theorems.Thm_KnodelPrimeCordial_cyclic_case_mod_10_counts__p2m_99de8117_516f_47d8_af56_8278a3d9be12_a2
-- name    : KnodelPrimeCordial.cyclic_case_mod_10_counts__p2m_99de8117_516f_47d8_af56_8278a3d9be12_a2
-- status  : Open
-- author  : @parclytaxel
-- created : 2026-11-16T10:31:37.184205+00:00
-- url     : https://prove2.me/theorems/9c307d6d-3fd4-4597-abb0-7474cd510ca5
-- title:
--   Edge counts for the corrected residue-10 labeling
-- statement:
--   For even n ≥ 10 with n % 12 = 10, the corrected labeling has (3(n / 2) + 1) / 2 cyclic-model edges with endpoint-label gcd greater than one and (3(n / 2)) / 2 edges with endpoint-label gcd equal to one. Prove by residue enumeration, including modulo-n boundary edges, undirected-edge uniqueness, and the correction at n − 3.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.cyclic_case_mod_10_counts__p2m_99de8117_516f_47d8_af56_8278a3d9be12_a2
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 10) :
    (KnodelPrimeCordial.edgesLabelZero (KnodelPrimeCordial.cyc n)
      (fun i : Fin n =>
        if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val)).card =
        (3 * (n / 2) + 1) / 2 ∧
      (KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.cyc n)
        (fun i : Fin n =>
          if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val)).card =
        (3 * (n / 2)) / 2 := by
  sorry
