-- Prove2me | Theorems.Thm_KnodelPrimeCordial_offset_edges_bijective__p2m_fceb7f73_3902_4bd2_af88_8120bd65169e_a2
-- name    : KnodelPrimeCordial.offset_edges_bijective__p2m_fceb7f73_3902_4bd2_af88_8120bd65169e_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:22:41.120821+00:00
-- url     : https://prove2.me/theorems/59f38484-bb00-4027-bdbb-b5bd99d88ac0
-- title:
--   Knödel edges are uniquely parametrized by offsets
-- statement:
--   For `4 ≤ n / 2`, every edge of `knodel 3 n` has a unique representation by a left-side index and one of the three offsets.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel

theorem KnodelPrimeCordial.offset_edges_bijective__p2m_fceb7f73_3902_4bd2_af88_8120bd65169e_a2 (n : ℕ) (h4 : 4 ≤ n / 2) :
    Set.BijOn
      (fun p : Fin (n / 2) × Fin 3 =>
        s(⟨(0 : Fin 2), p.1⟩,
          ⟨(1 : Fin 2),
            ⟨(p.1.val + 2 ^ p.2.val - 1) % (n / 2), Nat.mod_lt _ (by omega)⟩⟩))
      Set.univ
      (↑((KnodelPrimeCordial.knodel 3 n).edgeFinset) :
        Set (Sym2 (Fin 2 × Fin (n / 2)))) := by sorry
