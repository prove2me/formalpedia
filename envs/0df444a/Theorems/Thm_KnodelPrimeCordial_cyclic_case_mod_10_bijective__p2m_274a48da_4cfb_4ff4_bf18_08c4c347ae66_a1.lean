-- Prove2me | Theorems.Thm_KnodelPrimeCordial_cyclic_case_mod_10_bijective__p2m_274a48da_4cfb_4ff4_bf18_08c4c347ae66_a1
-- name    : KnodelPrimeCordial.cyclic_case_mod_10_bijective__p2m_274a48da_4cfb_4ff4_bf18_08c4c347ae66_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T10:15:49.155331+00:00
-- url     : https://prove2.me/theorems/6dfc39c6-04b4-4470-a7a0-9be6cdfdbf5c
-- title:
--   Bijection of the corrected residue-10 labeling
-- statement:
--   For even n ≥ 10 with n % 12 = 10, the endpoint-corrected labeling maps Fin n bijectively onto the integers from 1 through n.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.cyclic_case_mod_10_bijective__p2m_274a48da_4cfb_4ff4_bf18_08c4c347ae66_a1 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 10) :
    Set.BijOn
      (fun i : Fin n => if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val)
      Set.univ (Set.Icc 1 n) := by sorry
