-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_6_label_edge_count_sum__p2m_bd2bd721_d798_4454_857d_a78e8064bab2_a1
-- name    : KnodelPrimeCordial.case_mod_6_label_edge_count_sum__p2m_bd2bd721_d798_4454_857d_a78e8064bab2_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T10:20:18.440203+00:00
-- url     : https://prove2.me/theorems/58793991-d9f6-4cd5-bcae-633aaf737148
-- title:
--   Total edge-label count for the residue-six labeling
-- statement:
--   For the same n and labeling, the two edge-label counts sum to 3n/2, the number of edges in the cubic Knödel graph. A proof route establishes positivity of the labeling, applies the existing proved theorem that positive edge gcds partition the edge set into the two classes, and counts the edges by the three distinct offsets 0, 1, and 3. This sum result together with the non-coprime count determines the coprime count.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_edge_label_partition__p2m_730717b0_dc72_4b0f_b59f_ead0370cbb16_a1

theorem KnodelPrimeCordial.case_mod_6_label_edge_count_sum__p2m_bd2bd721_d798_4454_857d_a78e8064bab2_a1 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) : (KnodelPrimeCordial.edgesLabelZero (KnodelPrimeCordial.knodel 3 n) (fun v : Fin 2 × Fin (n / 2) => KnodelPrimeCordial.labelF (if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n))).card + (KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.knodel 3 n) (fun v : Fin 2 × Fin (n / 2) => KnodelPrimeCordial.labelF (if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n))).card = 3 * n / 2 := by sorry
