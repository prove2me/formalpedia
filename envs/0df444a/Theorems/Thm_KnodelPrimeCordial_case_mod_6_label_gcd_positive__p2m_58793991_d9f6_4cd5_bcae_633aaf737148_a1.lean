-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_6_label_gcd_positive__p2m_58793991_d9f6_4cd5_bcae_633aaf737148_a1
-- name    : KnodelPrimeCordial.case_mod_6_label_gcd_positive__p2m_58793991_d9f6_4cd5_bcae_633aaf737148_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T10:53:18.916293+00:00
-- url     : https://prove2.me/theorems/1345033d-f6c8-4911-94c2-fee483b819e1
-- title:
--   Positivity of the edge gcds for the residue-six labeling
-- statement:
--   For every edge of the defined Knödel graph, the gcd of the endpoint labels under the specified residue-six labeling is positive.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling

theorem KnodelPrimeCordial.case_mod_6_label_gcd_positive__p2m_58793991_d9f6_4cd5_bcae_633aaf737148_a1 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) : ∀ e ∈ (KnodelPrimeCordial.knodel 3 n).edgeFinset, 0 < KnodelPrimeCordial.edgeGcd (fun v : Fin 2 × Fin (n / 2) => KnodelPrimeCordial.labelF (if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n)) e := by sorry
