-- Prove2me | Theorems.Thm_KnodelPrimeCordial_knodel_3_8_edge_label_counts_sum_12__p2m_2ca607db_fb22_40a0_9812_c6037365c324_a3
-- name    : KnodelPrimeCordial.knodel_3_8_edge_label_counts_sum_12__p2m_2ca607db_fb22_40a0_9812_c6037365c324_a3
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T09:43:12.515043+00:00
-- url     : https://prove2.me/theorems/730717b0-dc72-4b0f-b59f-ead0370cbb16
-- title:
--   The two edge-label counts sum to 12
-- statement:
--   For every labeling bijective onto `1,…,8`, the counts of edges whose endpoint gcd is greater than one and equal to one sum to 12. The hypotheses give positive endpoint labels, so these two edge filters partition the 12-edge graph.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.1, p.3 (PDF p.3)

import Mathlib
import Definitions.Def_KnodelPrimeCordial_PrimeCordial
import Definitions.Def_KnodelPrimeCordial_knodel

theorem KnodelPrimeCordial.knodel_3_8_edge_label_counts_sum_12__p2m_2ca607db_fb22_40a0_9812_c6037365c324_a3 (f : Fin 2 × Fin 4 → ℕ) (hbij : Set.BijOn f Set.univ (Set.Icc 1 8)) : (KnodelPrimeCordial.edgesLabelZero (KnodelPrimeCordial.knodel 3 8) f).card + (KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.knodel 3 8) f).card = 12 := by sorry
