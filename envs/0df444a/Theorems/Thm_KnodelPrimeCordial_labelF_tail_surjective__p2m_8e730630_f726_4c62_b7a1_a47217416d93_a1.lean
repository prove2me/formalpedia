-- Prove2me | Theorems.Thm_KnodelPrimeCordial_labelF_tail_surjective__p2m_8e730630_f726_4c62_b7a1_a47217416d93_a1
-- name    : KnodelPrimeCordial.labelF_tail_surjective__p2m_8e730630_f726_4c62_b7a1_a47217416d93_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T10:33:42.653537+00:00
-- url     : https://prove2.me/theorems/ae64333b-fe93-47b0-ae2c-cfe5bec6348b
-- title:
--   The corrected final block covers its ten labels
-- statement:
--   For every q, the final ten indices of a block of length 12 attain the labels 12q+1 through 12q+10 when the index 12q+7 is assigned the corrected value i+3.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.labelF_tail_surjective__p2m_8e730630_f726_4c62_b7a1_a47217416d93_a1 (q y : ℕ) (hlo : 12 * q < y) (hhi : y ≤ 12 * q + 10) : ∃ i : ℕ, i < 12 * q + 10 ∧ (if i = 12 * q + 7 then i + 3 else KnodelPrimeCordial.labelF i) = y := by sorry
