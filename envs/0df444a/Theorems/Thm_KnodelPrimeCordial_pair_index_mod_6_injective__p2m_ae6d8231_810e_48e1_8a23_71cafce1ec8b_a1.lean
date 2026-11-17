-- Prove2me | Theorems.Thm_KnodelPrimeCordial_pair_index_mod_6_injective__p2m_ae6d8231_810e_48e1_8a23_71cafce1ec8b_a1
-- name    : KnodelPrimeCordial.pair_index_mod_6_injective__p2m_ae6d8231_810e_48e1_8a23_71cafce1ec8b_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T10:37:17.732748+00:00
-- url     : https://prove2.me/theorems/7de6a5f1-5378-4bcd-8203-21daaa5c1512
-- title:
--   The pair indexing is injective
-- statement:
--   Under the target hypotheses, the pair-index function takes distinct pairs to distinct residues.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib

theorem KnodelPrimeCordial.pair_index_mod_6_injective__p2m_ae6d8231_810e_48e1_8a23_71cafce1ec8b_a1 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    Set.InjOn
      (fun v : Fin 2 × Fin (n / 2) =>
        if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n)
      Set.univ := by sorry
