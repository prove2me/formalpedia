-- Prove2me | Theorems.Thm_KnodelPrimeCordial_labelF_prefix_surjective__p2m_8e730630_f726_4c62_b7a1_a47217416d93_a1
-- name    : KnodelPrimeCordial.labelF_prefix_surjective__p2m_8e730630_f726_4c62_b7a1_a47217416d93_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T10:33:39.74921+00:00
-- url     : https://prove2.me/theorems/7c638a40-aa1b-4e3b-9a8c-79f3dcff308e
-- title:
--   The labeling covers each complete block prefix
-- statement:
--   For every natural number q, the indices below 12q under labelF attain every label from 1 through 12q.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.labelF_prefix_surjective__p2m_8e730630_f726_4c62_b7a1_a47217416d93_a1 (q y : ℕ) (hy : y ∈ Set.Icc 1 (12 * q)) : ∃ i : ℕ, i < 12 * q ∧ KnodelPrimeCordial.labelF i = y := by sorry
