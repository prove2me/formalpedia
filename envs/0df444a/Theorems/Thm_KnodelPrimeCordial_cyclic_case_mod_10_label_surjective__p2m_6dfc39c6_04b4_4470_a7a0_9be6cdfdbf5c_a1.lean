-- Prove2me | Theorems.Thm_KnodelPrimeCordial_cyclic_case_mod_10_label_surjective__p2m_6dfc39c6_04b4_4470_a7a0_9be6cdfdbf5c_a1
-- name    : KnodelPrimeCordial.cyclic_case_mod_10_label_surjective__p2m_6dfc39c6_04b4_4470_a7a0_9be6cdfdbf5c_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T10:24:57.115095+00:00
-- url     : https://prove2.me/theorems/8e730630-f726-4c62-b7a1-a47217416d93
-- title:
--   The corrected residue-10 labeling reaches every target label
-- statement:
--   Every integer from 1 through n is the label of some index.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.cyclic_case_mod_10_label_surjective__p2m_6dfc39c6_04b4_4470_a7a0_9be6cdfdbf5c_a1
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 10) :
    ∀ y : ℕ, y ∈ Set.Icc 1 n →
      ∃ i : Fin n,
        (if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val) = y := by sorry
