-- Prove2me | Theorems.Thm_GoldbergTarjan_FIFO_label_le_two_n_sub_one
-- name    : GoldbergTarjan.FIFO.label_le_two_n_sub_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:35:40.781737+00:00
-- url     : https://prove2.me/theorems/bca1d4ea-e37c-4c1f-984c-df350d3a0639
-- title:
--   Lemma 3.7 — every distance label stays at most $2n - 1$ (first-in, first-out algorithm)
-- statement:
--   Let $n = |V|$. In every run of the first-in, first-out algorithm, at any time during the execution and for every vertex $v \in V$, $$d(v) \le 2n - 1.$$ "At any time" covers the states between consecutive discharges and every configuration between two push/relabel operations inside a discharge.
--
--   In particular labels never become infinite. The bound is what limits the number of relabelings (Lemma 3.8) and, through it, the number of passes (Lemma 4.3).
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, p. 927, Lemma 3.7

import Mathlib
import Definitions.Def_GoldbergTarjan_FIFO_Network
import Definitions.Def_GoldbergTarjan_FIFO_PushRelabel
import Definitions.Def_GoldbergTarjan_FIFO_Algorithm
import Definitions.Def_GoldbergTarjan_FIFO_Counts

namespace GoldbergTarjan.FIFO

/-- Lemma 3.7 (Goldberg–Tarjan 1988, p. 927), for the first-in, first-out algorithm: at any time
during the execution of the algorithm and for any vertex `v ∈ V`, `d(v) ≤ 2n − 1`, where
`n = |V|`. "At any time" covers the states between discharges and the configurations between
the push/relabel operations inside each discharge. -/
theorem label_le_two_n_sub_one {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (L : V → List V) (K : ℕ) (S : ℕ → State V) (J : ℕ → ℕ)
    (hrun : IsFIFORun N L K S J) :
    (∀ k ≤ K, ∀ v, (S k).cfg.d v ≤ ((2 * Fintype.card V - 1 : ℕ) : ℕ∞)) ∧
    (∀ k < K, ∀ j ≤ J k, ∀ v,
      (prIter N L (frontVertex N (S k)) (S k).cfg j).d v
        ≤ ((2 * Fintype.card V - 1 : ℕ) : ℕ∞)) := by sorry

end GoldbergTarjan.FIFO
