-- Prove2me | Theorems.Thm_KnodelPrimeCordial_edge_gcd_positive_from_bij__p2m_730717b0_dc72_4b0f_b59f_ead0370cbb16_a1
-- name    : KnodelPrimeCordial.edge_gcd_positive_from_bij__p2m_730717b0_dc72_4b0f_b59f_ead0370cbb16_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T09:46:59.434114+00:00
-- url     : https://prove2.me/theorems/db98ee71-cb3b-4c1a-8354-2f69c6fa8827
-- title:
--   Positive edge gcds from a labeling bijection
-- statement:
--   Every edge of `knodel 3 8` has positive endpoint gcd when the vertex labels are bijective onto `1,…,8`.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.1, p.3 (PDF p.3)

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel

theorem KnodelPrimeCordial.edge_gcd_positive_from_bij__p2m_730717b0_dc72_4b0f_b59f_ead0370cbb16_a1 (f : Fin 2 × Fin 4 → ℕ) (hbij : Set.BijOn f Set.univ (Set.Icc 1 8)) : ∀ e ∈ (KnodelPrimeCordial.knodel 3 8).edgeFinset, 0 < KnodelPrimeCordial.edgeGcd f e := by sorry
