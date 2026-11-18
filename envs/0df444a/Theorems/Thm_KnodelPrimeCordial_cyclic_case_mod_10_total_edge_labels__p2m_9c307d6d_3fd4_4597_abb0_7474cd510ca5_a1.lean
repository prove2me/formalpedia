-- Prove2me | Theorems.Thm_KnodelPrimeCordial_cyclic_case_mod_10_total_edge_labels__p2m_9c307d6d_3fd4_4597_abb0_7474cd510ca5_a1
-- name    : KnodelPrimeCordial.cyclic_case_mod_10_total_edge_labels__p2m_9c307d6d_3fd4_4597_abb0_7474cd510ca5_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-17T17:13:32.050195+00:00
-- url     : https://prove2.me/theorems/81f948ee-36ea-4285-a2f8-fddc3693e406
-- title:
--   Total edge-label count for the corrected residue-10 labeling
-- statement:
--   For even n ≥ 10 with n modulo 12 equal to 10, the two edge-label classes of the corrected cyclic labeling together contain 3(n/2) edges. This supplies the total needed alongside the balance bound to derive each exact count.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.cyclic_case_mod_10_total_edge_labels__p2m_9c307d6d_3fd4_4597_abb0_7474cd510ca5_a1
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 10) :
    (KnodelPrimeCordial.edgesLabelZero (KnodelPrimeCordial.cyc n)
      (fun i : Fin n =>
        if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val)).card +
      (KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.cyc n)
        (fun i : Fin n =>
          if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val)).card =
        3 * (n / 2) := by sorry
