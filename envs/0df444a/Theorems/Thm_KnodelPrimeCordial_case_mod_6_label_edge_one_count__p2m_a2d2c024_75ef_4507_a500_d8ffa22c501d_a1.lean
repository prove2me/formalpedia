-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_6_label_edge_one_count__p2m_a2d2c024_75ef_4507_a500_d8ffa22c501d_a1
-- name    : KnodelPrimeCordial.case_mod_6_label_edge_one_count__p2m_a2d2c024_75ef_4507_a500_d8ffa22c501d_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T10:54:30.576605+00:00
-- url     : https://prove2.me/theorems/42c92209-5c01-4247-acfb-35cad623a7ea
-- title:
--   Coprime-edge count for the residue-six labeling
-- statement:
--   For this residue-six labeling, the number of edges whose endpoint labels are coprime is `(3 * n + 2) / 4`. This independent count isolates the gcd and wraparound enumeration needed by the parent.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.case_mod_6_label_edge_one_count__p2m_a2d2c024_75ef_4507_a500_d8ffa22c501d_a1 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) : (KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.knodel 3 n) (fun v : Fin 2 × Fin (n / 2) => KnodelPrimeCordial.labelF (if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n))).card = (3 * n + 2) / 4 := by sorry
