-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_2_residue_1_pointwise_coprime__p2m_da97d3f1_256c_4f52_83d8_9a648f286d22_a1
-- name    : KnodelPrimeCordial.case_mod_6_offset_2_residue_1_pointwise_coprime__p2m_da97d3f1_256c_4f52_83d8_9a648f286d22_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:40:42.131485+00:00
-- url     : https://prove2.me/theorems/0a6fbe1e-0dc0-47dd-8ce3-6f9bdc92082e
-- title:
--   Pointwise coprimality in residue class one
-- statement:
--   Under the target hypotheses, every index in residue class one has coprime endpoint labels for the specified offset-two edge. Writing n = 12q + 6, the ordinary indices yield labels 12t+5 and 12t+11; the final index wraps and yields labels 12q+5 and 4. The child removes the label and gcd calculation from the parent.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.case_mod_6_offset_2_residue_1_pointwise_coprime__p2m_da97d3f1_256c_4f52_83d8_9a648f286d22_a1
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6)
    (j : Fin (n / 2)) (hj : j.val % 6 = 1) :
    Nat.Coprime
      (KnodelPrimeCordial.labelF (2 * j.val))
      (KnodelPrimeCordial.labelF
        ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n)) := by sorry
