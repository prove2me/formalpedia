-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_6_edge_count__p2m_58793991_d9f6_4cd5_bcae_633aaf737148_a1
-- name    : KnodelPrimeCordial.case_mod_6_edge_count__p2m_58793991_d9f6_4cd5_bcae_633aaf737148_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T10:53:22.405688+00:00
-- url     : https://prove2.me/theorems/411d5a68-c305-475b-bbd0-563e10602942
-- title:
--   Edge count of the degree-three Knödel graph
-- statement:
--   Under the stated hypotheses, the graph `knodel 3 n` has exactly `3 * n / 2` unordered edges.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel

theorem KnodelPrimeCordial.case_mod_6_edge_count__p2m_58793991_d9f6_4cd5_bcae_633aaf737148_a1 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) : (KnodelPrimeCordial.knodel 3 n).edgeFinset.card = 3 * n / 2 := by sorry
