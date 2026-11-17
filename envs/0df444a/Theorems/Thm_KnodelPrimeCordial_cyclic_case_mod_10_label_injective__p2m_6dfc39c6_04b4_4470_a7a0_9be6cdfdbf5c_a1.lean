-- Prove2me | Theorems.Thm_KnodelPrimeCordial_cyclic_case_mod_10_label_injective__p2m_6dfc39c6_04b4_4470_a7a0_9be6cdfdbf5c_a1
-- name    : KnodelPrimeCordial.cyclic_case_mod_10_label_injective__p2m_6dfc39c6_04b4_4470_a7a0_9be6cdfdbf5c_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T10:25:13.072196+00:00
-- url     : https://prove2.me/theorems/80c90d65-a0f5-45ab-ba71-89f4cde630ee
-- title:
--   The corrected residue-10 labeling is injective
-- statement:
--   Distinct indices receive distinct labels.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.cyclic_case_mod_10_label_injective__p2m_6dfc39c6_04b4_4470_a7a0_9be6cdfdbf5c_a1
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 10) :
    Function.Injective
      (fun i : Fin n => if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val) := by sorry
