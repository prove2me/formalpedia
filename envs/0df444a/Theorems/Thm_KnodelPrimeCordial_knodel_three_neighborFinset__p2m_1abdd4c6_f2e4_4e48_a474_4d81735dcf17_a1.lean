-- Prove2me | Theorems.Thm_KnodelPrimeCordial_knodel_three_neighborFinset__p2m_1abdd4c6_f2e4_4e48_a474_4d81735dcf17_a1
-- name    : KnodelPrimeCordial.knodel_three_neighborFinset__p2m_1abdd4c6_f2e4_4e48_a474_4d81735dcf17_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:37:22.455173+00:00
-- url     : https://prove2.me/theorems/9cd968dd-251a-4b31-b9e6-6fca83fa236c
-- title:
--   Neighbor finset for a side-zero vertex in the degree-three Knödel graph
-- statement:
--   The neighbors of (0,j) are exactly the opposite-side vertices with indices j, j+1, and j+3 reduced modulo n/2. This follows by unfolding adjacency and considering the three possible values of k below 3. The modulus is positive under the stated lower bound.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel

theorem KnodelPrimeCordial.knodel_three_neighborFinset__p2m_1abdd4c6_f2e4_4e48_a474_4d81735dcf17_a1 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (j : Fin (n / 2)) : (KnodelPrimeCordial.knodel 3 n).neighborFinset (0, j) = {(1, j), (1, ⟨(j.val + 1) % (n / 2), Nat.mod_lt _ (by omega)⟩), (1, ⟨(j.val + 3) % (n / 2), Nat.mod_lt _ (by omega)⟩)} := by sorry
