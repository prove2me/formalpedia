-- Prove2me | Theorems.Thm_KnodelPrimeCordial_pair_index_mod_6_bijective__p2m_9ac481dd_4e35_42fc_b8a2_93d77d603321_a2
-- name    : KnodelPrimeCordial.pair_index_mod_6_bijective__p2m_9ac481dd_4e35_42fc_b8a2_93d77d603321_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T10:29:21.977031+00:00
-- url     : https://prove2.me/theorems/ae6d8231-810e-48e1-8a23-71cafce1ec8b
-- title:
--   The pair indexing enumerates all indices
-- statement:
--   For even `n ≥ 10` with `n % 12 = 6`, the pair-index formula bijects the vertex pairs with the indices from `0` to `n−1`. The first side gives the even residues and the second gives the odd residues, including the wraparound value `n−1`.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib

theorem KnodelPrimeCordial.pair_index_mod_6_bijective__p2m_9ac481dd_4e35_42fc_b8a2_93d77d603321_a2 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    Set.BijOn
      (fun v : Fin 2 × Fin (n / 2) =>
        if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n)
      Set.univ (Set.Icc 0 (n - 1)) := by sorry
