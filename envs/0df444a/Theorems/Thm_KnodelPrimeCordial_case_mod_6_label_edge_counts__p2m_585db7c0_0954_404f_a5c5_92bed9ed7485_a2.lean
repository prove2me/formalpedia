-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_6_label_edge_counts__p2m_585db7c0_0954_404f_a5c5_92bed9ed7485_a2
-- name    : KnodelPrimeCordial.case_mod_6_label_edge_counts__p2m_585db7c0_0954_404f_a5c5_92bed9ed7485_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T10:02:27.548294+00:00
-- url     : https://prove2.me/theorems/bd2bd721-d798-4454-857d-a78e8064bab2
-- title:
--   Edge counts for the residue-six labeling
-- statement:
--   For the proposed residue-six labeling, the number of edges with endpoint-label gcd greater than one is `(3*n - 2)/4`, and the number with gcd equal to one is `(3*n + 2)/4`. A proof maps the Knödel edges to cycle edges and even-indexed `+5` chords, counts by starting index modulo twelve, and includes the wraparound edges. The resulting counts differ by exactly one.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.case_mod_6_label_edge_counts__p2m_585db7c0_0954_404f_a5c5_92bed9ed7485_a2 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) : (KnodelPrimeCordial.edgesLabelZero (KnodelPrimeCordial.knodel 3 n) (fun v : Fin 2 × Fin (n / 2) => KnodelPrimeCordial.labelF (if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n))).card = (3 * n - 2) / 4 ∧ (KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.knodel 3 n) (fun v : Fin 2 × Fin (n / 2) => KnodelPrimeCordial.labelF (if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n))).card = (3 * n + 2) / 4 := by sorry
