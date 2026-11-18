-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_4__p2m_be27a6d0_01d1_46f0_b9ba_0d15398f9cfb_a1
-- name    : KnodelPrimeCordial.case_mod_4__p2m_be27a6d0_01d1_46f0_b9ba_0d15398f9cfb_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T09:39:16.109197+00:00
-- url     : https://prove2.me/theorems/d9f15af7-7b55-4a90-9aa3-c03a2c2d26cd
-- title:
--   Prime cordiality in residue class 4 modulo 12
-- statement:
--   For even `n ≥ 10` with `n % 12 = 4`, `knodel 3 n` has a prime cordial labeling. Prove this by constructing the residue-four labeling, checking its bijection and edge-count balance, including boundary edges.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_PrimeCordial
import Definitions.Def_KnodelPrimeCordial_knodel

theorem KnodelPrimeCordial.case_mod_4__p2m_be27a6d0_01d1_46f0_b9ba_0d15398f9cfb_a1 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 4) : KnodelPrimeCordial.PrimeCordial (KnodelPrimeCordial.knodel 3 n) := by sorry
