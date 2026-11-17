-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_2_residue_1_index_count__p2m_da97d3f1_256c_4f52_83d8_9a648f286d22_a1
-- name    : KnodelPrimeCordial.case_mod_6_offset_2_residue_1_index_count__p2m_da97d3f1_256c_4f52_83d8_9a648f286d22_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:40:42.603499+00:00
-- url     : https://prove2.me/theorems/eea8c874-7b73-419c-bcde-710fd0148980
-- title:
--   Index count in residue class one
-- statement:
--   Under the target hypotheses, exactly n/12+1 indices in Fin (n/2) have value congruent to one modulo six. For n = 12q+6 these are 6t+1 for 0 ≤ t ≤ q. This child supplies the finite cardinality calculation used after the parent identifies the two filters.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.case_mod_6_offset_2_residue_1_index_count__p2m_da97d3f1_256c_4f52_83d8_9a648f286d22_a1
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    (Finset.univ.filter fun j : Fin (n / 2) => j.val % 6 = 1).card = n / 12 + 1 := by sorry
