-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_6_edge_count_by_offsets__p2m_8a6c92bd_7c8f_41ac_9c83_07dd1e357c6c_a1
-- name    : KnodelPrimeCordial.case_mod_6_edge_count_by_offsets__p2m_8a6c92bd_7c8f_41ac_9c83_07dd1e357c6c_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:10:57.92023+00:00
-- url     : https://prove2.me/theorems/fceb7f73-3902-4bd2-af88-8120bd65169e
-- title:
--   Count coprime Knödel edges by neighbor offset
-- statement:
--   For any labeling of the vertices of `knodel 3 n`, when `n / 2 ≥ 4`, the number of edges with coprime endpoint labels equals the sum over the three neighbor offsets of the number of left vertices whose corresponding right neighbor has a coprime label.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF

open scoped BigOperators

theorem KnodelPrimeCordial.case_mod_6_edge_count_by_offsets__p2m_8a6c92bd_7c8f_41ac_9c83_07dd1e357c6c_a1 (n : ℕ) (h4 : 4 ≤ n / 2) (f : Fin 2 × Fin (n / 2) → ℕ) :
    (KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.knodel 3 n) f).card =
      ∑ k : Fin 3,
        (Finset.univ.filter fun j : Fin (n / 2) =>
          Nat.Coprime
            (f ⟨(0 : Fin 2), j⟩)
            (f
              ⟨(1 : Fin 2),
                ⟨(j.val + 2 ^ k.val - 1) % (n / 2), Nat.mod_lt _ (by omega)⟩⟩)).card := by sorry
