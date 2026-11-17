-- Prove2me | Theorems.Thm_KnodelPrimeCordial_knodel_3_8_coprime_edge_lower_bound__p2m_2ca607db_fb22_40a0_9812_c6037365c324_a3
-- name    : KnodelPrimeCordial.knodel_3_8_coprime_edge_lower_bound__p2m_2ca607db_fb22_40a0_9812_c6037365c324_a3
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T09:43:12.816675+00:00
-- url     : https://prove2.me/theorems/a761614d-f372-42a3-bd68-c80e83f4ad67
-- title:
--   At least seven edges have coprime endpoint labels
-- statement:
--   For every labeling bijective onto `1,…,8`, at least seven edges have coprime endpoint labels. The proof selects the vertices labeled 1, 5, and 7. Their incident edges are coprime; their degree sum is nine, and bipartiteness bounds their internal edges by two, giving at least seven distinct incident edges.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.1, p.3 (PDF p.3)

import Mathlib
import Definitions.Def_KnodelPrimeCordial_PrimeCordial
import Definitions.Def_KnodelPrimeCordial_knodel

theorem KnodelPrimeCordial.knodel_3_8_coprime_edge_lower_bound__p2m_2ca607db_fb22_40a0_9812_c6037365c324_a3 (f : Fin 2 × Fin 4 → ℕ) (hbij : Set.BijOn f Set.univ (Set.Icc 1 8)) : 7 ≤ (KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.knodel 3 8) f).card := by sorry
