-- Prove2me | Theorems.Thm_KnodelPrimeCordial_labelF_range_blocks__p2m_7c638a40_aa1b_4e3b_9a8c_79f3dcff308e_a1
-- name    : KnodelPrimeCordial.labelF_range_blocks__p2m_7c638a40_aa1b_4e3b_9a8c_79f3dcff308e_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T10:55:31.855657+00:00
-- url     : https://prove2.me/theorems/142a0821-65c5-4def-8061-45e2a4b549cd
-- title:
--   Labels in the range lie in one of the first q blocks
-- statement:
--   Every natural number y from 1 through 12q belongs to a block with number k<q and an offset t from 1 through 12.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib

theorem KnodelPrimeCordial.labelF_range_blocks__p2m_7c638a40_aa1b_4e3b_9a8c_79f3dcff308e_a1 (q y : ℕ) (hy : y ∈ Set.Icc 1 (12 * q)) : ∃ k t : ℕ, k < q ∧ t ∈ Set.Icc 1 12 ∧ y = 12 * k + t := by sorry
