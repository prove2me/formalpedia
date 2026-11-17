-- Prove2me | Theorems.Thm_KnodelPrimeCordial_cyclic_label_transport__p2m_2c82152f_23cb_4c50_aa74_3d1d5ac827a4_a2
-- name    : KnodelPrimeCordial.cyclic_label_transport__p2m_2c82152f_23cb_4c50_aa74_3d1d5ac827a4_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T10:06:17.21694+00:00
-- url     : https://prove2.me/theorems/b71a112c-d89d-4dc4-9a88-bb82c5bac86c
-- title:
--   Transport prime cordial labelings from the cyclic model
-- statement:
--   For even n ≥ 10, every prime cordial labeling of the cyclic model `cyc n` induces a prime cordial labeling of `knodel 3 n`.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_vtx

theorem KnodelPrimeCordial.cyclic_label_transport__p2m_2c82152f_23cb_4c50_aa74_3d1d5ac827a4_a2
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n)
    (f : Fin n → ℕ) (hf : KnodelPrimeCordial.IsPrimeCordialLabeling
      (KnodelPrimeCordial.cyc n) f) :
    ∃ g : Fin 2 × Fin (n / 2) → ℕ,
      KnodelPrimeCordial.IsPrimeCordialLabeling (KnodelPrimeCordial.knodel 3 n) g := by sorry
