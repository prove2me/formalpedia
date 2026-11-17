-- Prove2me | Theorems.Thm_KnodelPrimeCordial_knodel_3_8_incident_edges_are_coprime__p2m_a761614d_f372_42a3_bd68_c80e83f4ad67_a2
-- name    : KnodelPrimeCordial.knodel_3_8_incident_edges_are_coprime__p2m_a761614d_f372_42a3_bd68_c80e83f4ad67_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T09:59:14.194129+00:00
-- url     : https://prove2.me/theorems/df77e916-fdac-4de2-9395-a46d11d6721f
-- title:
--   Edges incident to labels 1, 5, or 7 are coprime
-- statement:
--   Under a bijection onto `1,…,8`, every edge incident to a vertex labeled `1`, `5`, or `7` has coprime endpoint labels.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.1, p.3 (PDF p.3)

import Mathlib
import Definitions.Def_KnodelPrimeCordial_PrimeCordial
import Definitions.Def_KnodelPrimeCordial_knodel

theorem KnodelPrimeCordial.knodel_3_8_incident_edges_are_coprime__p2m_a761614d_f372_42a3_bd68_c80e83f4ad67_a2 (f : Fin 2 × Fin 4 → ℕ) (hbij : Set.BijOn f Set.univ (Set.Icc 1 8)) (x y z : Fin 2 × Fin 4) (hx : f x = 1) (hy : f y = 5) (hz : f z = 7) :
    ((KnodelPrimeCordial.knodel 3 8).edgeFinset.filter (fun e => x ∈ e ∨ y ∈ e ∨ z ∈ e)) ⊆
      KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.knodel 3 8) f := by sorry
