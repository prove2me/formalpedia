-- Prove2me | Theorems.Thm_KnodelPrimeCordial_knodel_3_8_edge_count__p2m_730717b0_dc72_4b0f_b59f_ead0370cbb16_a1
-- name    : KnodelPrimeCordial.knodel_3_8_edge_count__p2m_730717b0_dc72_4b0f_b59f_ead0370cbb16_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T09:46:59.054742+00:00
-- url     : https://prove2.me/theorems/dde2f105-4e9a-40d9-93c0-f06edddae2c2
-- title:
--   The Knödel graph W₃,₈ has 12 edges
-- statement:
--   The graph `knodel 3 8` has 12 undirected edges.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.1, p.3 (PDF p.3)

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel

theorem KnodelPrimeCordial.knodel_3_8_edge_count__p2m_730717b0_dc72_4b0f_b59f_ead0370cbb16_a1 : (KnodelPrimeCordial.knodel 3 8).edgeFinset.card = 12 := by sorry
