-- Prove2me | Theorems.Thm_KnodelPrimeCordial_cyclic_case_mod_10__p2m_2c82152f_23cb_4c50_aa74_3d1d5ac827a4_a2
-- name    : KnodelPrimeCordial.cyclic_case_mod_10__p2m_2c82152f_23cb_4c50_aa74_3d1d5ac827a4_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T10:06:09.576861+00:00
-- url     : https://prove2.me/theorems/274a48da-4cfb-4ff4-bf18-08c4c347ae66
-- title:
--   Cyclic labeling in residue class 10 modulo 12
-- statement:
--   For even n ≥ 10 with n % 12 = 10, the explicit endpoint-corrected `labelF` labeling of the cyclic graph is bijective onto 1,…,n and its two edge-label counts differ by at most one.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.cyclic_case_mod_10__p2m_2c82152f_23cb_4c50_aa74_3d1d5ac827a4_a2 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 10) :
    Set.BijOn
        (fun i : Fin n => if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val)
        Set.univ (Set.Icc 1 n) ∧
      |((KnodelPrimeCordial.edgesLabelZero (KnodelPrimeCordial.cyc n)
          (fun i : Fin n =>
            if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val)).card : ℤ) -
        ((KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.cyc n)
          (fun i : Fin n =>
            if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val)).card : ℤ)| ≤ 1 := by sorry
