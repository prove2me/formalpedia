-- Prove2me | Theorems.Thm_KnodelPrimeCordial_knodel_three_regular_side1__p2m_9dfa4dbf_1cc5_4722_9f1c_fa72524f7381_a2
-- name    : KnodelPrimeCordial.knodel_three_regular_side1__p2m_9dfa4dbf_1cc5_4722_9f1c_fa72524f7381_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:24:27.315111+00:00
-- url     : https://prove2.me/theorems/165d50bc-4001-44b9-bb11-e1f7ef0e1992
-- title:
--   Degree three for vertices on side one
-- statement:
--   For even n at least 10, a vertex (1,j) has exactly three neighbors. Reversing the adjacency equation gives the opposite-side indices j, j−1, and j−3 modulo n/2; the modulus is at least 5, so these indices are distinct. Counting this neighbor set establishes the degree.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel

theorem KnodelPrimeCordial.knodel_three_regular_side1__p2m_9dfa4dbf_1cc5_4722_9f1c_fa72524f7381_a2 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (j : Fin (n / 2)) : (KnodelPrimeCordial.knodel 3 n).degree (1, j) = 3 := by sorry
