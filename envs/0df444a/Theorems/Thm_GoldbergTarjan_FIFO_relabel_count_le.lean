-- Prove2me | Theorems.Thm_GoldbergTarjan_FIFO_relabel_count_le
-- name    : GoldbergTarjan.FIFO.relabel_count_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:36:13.646922+00:00
-- url     : https://prove2.me/theorems/cb30b1df-c44e-4c6a-bf6f-b56adcc082cc
-- title:
--   Lemma 3.8 — at most $2n - 1$ relabelings per vertex and $(2n-1)(n-2) < 2n^2$ overall (first-in, first-out algorithm)
-- statement:
--   Let $n = |V|$. In every run of the first-in, first-out algorithm, the number of relabeling operations is at most $2n - 1$ for each vertex, and in total
--   $$\#\{\text{relabelings}\} \le (2n-1)(n-2) < 2n^2.$$
--
--   A relabeling is a push/relabel operation that takes the relabeling branch of Fig. 3. The bound caps the total increase of the labels, which is the budget used to count passes in Lemma 4.3.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, p. 927, Lemma 3.8

import Mathlib
import Definitions.Def_GoldbergTarjan_FIFO_Network
import Definitions.Def_GoldbergTarjan_FIFO_PushRelabel
import Definitions.Def_GoldbergTarjan_FIFO_Algorithm
import Definitions.Def_GoldbergTarjan_FIFO_Counts

namespace GoldbergTarjan.FIFO

/-- Lemma 3.8 (Goldberg–Tarjan 1988, p. 927), for the first-in, first-out algorithm: the number of
relabeling operations is at most `2n − 1` per vertex and at most `(2n − 1)(n − 2) < 2n²`
overall, where `n = |V|`. The relabelings counted are the push/relabel operations of all
discharges of the run that take the relabeling branch of Fig. 3. -/
theorem relabel_count_le {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (L : V → List V) (K : ℕ) (S : ℕ → State V) (J : ℕ → ℕ)
    (hrun : IsFIFORun N L K S J) :
    (∀ x, relabelCountAt N L K S J x ≤ 2 * Fintype.card V - 1) ∧
    relabelCount N L K S J ≤ (2 * Fintype.card V - 1) * (Fintype.card V - 2) ∧
    (2 * Fintype.card V - 1) * (Fintype.card V - 2) < 2 * Fintype.card V ^ 2 := by sorry

end GoldbergTarjan.FIFO
