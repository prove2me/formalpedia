-- Prove2me | Theorems.Thm_KnodelPrimeCordial_knodel_three_regular__p2m_411d5a68_c305_475b_bbd0_563e10602942_a1
-- name    : KnodelPrimeCordial.knodel_three_regular__p2m_411d5a68_c305_475b_bbd0_563e10602942_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:00:25.330831+00:00
-- url     : https://prove2.me/theorems/9dfa4dbf-1cc5-4722-9f1c-fa72524f7381
-- title:
--   Every vertex of the degree-three Knödel graph has degree three
-- statement:
--   For every even natural number n at least 10, every vertex of the graph knodel 3 n has degree three.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel

theorem KnodelPrimeCordial.knodel_three_regular__p2m_411d5a68_c305_475b_bbd0_563e10602942_a1 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (v : Fin 2 × Fin (n / 2)) : (KnodelPrimeCordial.knodel 3 n).degree v = 3 := by sorry
