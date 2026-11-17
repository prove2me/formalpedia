-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_2_residue_5_label_values__p2m_44d4bacb_229b_4cd5_be6a_4744e1588199_a1
-- name    : KnodelPrimeCordial.case_mod_6_offset_2_residue_5_label_values__p2m_44d4bacb_229b_4cd5_be6a_4744e1588199_a1
-- status  : Disproved
-- author  : @parclytaxel
-- created : 2026-11-16T11:45:58.876342+00:00
-- url     : https://prove2.me/theorems/99b4b0bb-599f-4b7b-9b3f-1fd70cc31d45
-- title:
--   Labels and coprimality for class-five indices
-- statement:
--   For each in-range index in residue class five, the two endpoint labels are consecutive numbers, hence coprime; the `j + 3` modular step does not wrap.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.case_mod_6_offset_2_residue_5_label_values__p2m_44d4bacb_229b_4cd5_be6a_4744e1588199_a1
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6)
    (j : Fin (n / 2)) (hj : j.val % 6 = 5) :
    KnodelPrimeCordial.labelF (2 * j.val) = 2 * j.val + 2 ∧
      KnodelPrimeCordial.labelF
        ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n) = 2 * j.val + 3 ∧
      Nat.Coprime (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2) + n - 1) % n))) := by sorry
