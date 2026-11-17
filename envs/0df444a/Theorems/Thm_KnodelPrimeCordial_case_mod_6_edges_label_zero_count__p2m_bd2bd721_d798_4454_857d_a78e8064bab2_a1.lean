-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_6_edges_label_zero_count__p2m_bd2bd721_d798_4454_857d_a78e8064bab2_a1
-- name    : KnodelPrimeCordial.case_mod_6_edges_label_zero_count__p2m_bd2bd721_d798_4454_857d_a78e8064bab2_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T10:20:25.798485+00:00
-- url     : https://prove2.me/theorems/a2d2c024-75ef-4507-a500-d8ffa22c501d
-- title:
--   Non-coprime edge count for the residue-six labeling
-- statement:
--   For every even n ≥ 10 with n congruent to 6 modulo 12, the specified labeling gives exactly (3n−2)/4 edges whose endpoint-label gcd is greater than one. The proof route is to enumerate the three edge offsets in the Knödel graph and count the residue classes of their endpoint labels, including edges whose indices wrap around modulo n. The hypotheses ensure n ≥ 18, so the offsets 0, 1, and 3 define distinct neighbors.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.case_mod_6_edges_label_zero_count__p2m_bd2bd721_d798_4454_857d_a78e8064bab2_a1 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) : (KnodelPrimeCordial.edgesLabelZero (KnodelPrimeCordial.knodel 3 n) (fun v : Fin 2 × Fin (n / 2) => KnodelPrimeCordial.labelF (if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n))).card = (3 * n - 2) / 4 := by sorry
