-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_6_label_bijective__p2m_585db7c0_0954_404f_a5c5_92bed9ed7485_a2
-- name    : KnodelPrimeCordial.case_mod_6_label_bijective__p2m_585db7c0_0954_404f_a5c5_92bed9ed7485_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T10:02:22.183897+00:00
-- url     : https://prove2.me/theorems/9ac481dd-4e35-42fc-b8a2-93d77d603321
-- title:
--   Bijectivity of the residue-six labeling
-- statement:
--   For even `n ≥ 10` with `n % 12 = 6`, the proposed labeling, obtained by indexing the two sides cyclically and applying `labelF`, is a bijection onto `1,…,n`. The residue condition implies `n ≥ 18`, so the indexing modulus is nonzero. A proof splits the indices into complete blocks of twelve and the final six positions, checking that `labelF` permutes each corresponding interval of labels.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.case_mod_6_label_bijective__p2m_585db7c0_0954_404f_a5c5_92bed9ed7485_a2 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) : Set.BijOn (fun v : Fin 2 × Fin (n / 2) => KnodelPrimeCordial.labelF (if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n)) Set.univ (Set.Icc 1 n) := by sorry
