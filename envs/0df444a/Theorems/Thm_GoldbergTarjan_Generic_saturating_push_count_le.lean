-- Prove2me | Theorems.Thm_GoldbergTarjan_Generic_saturating_push_count_le
-- name    : GoldbergTarjan.Generic.saturating_push_count_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:30:14.41359+00:00
-- url     : https://prove2.me/theorems/cd209531-f72b-42e4-85a6-83130ea443b8
-- title:
--   Lemma 3.9 — at most $2nm$ saturating pushes
-- statement:
--   Let $N$ be a flow network with $n$ vertices and $m$ edges (pairs of positive capacity), and let $(f_0,d_0), \dots, (f_K,d_K)$ be an execution of the generic algorithm, started from the initial state of Fig. 2 with the simple labeling. Then the number of saturating pushes among its $K$ steps (pushes Push$(v,w)$ after which $r_f(v,w) = 0$) satisfies
--
--   $$\#\{\text{saturating pushes}\} \le 2nm.$$
--
--   This is the second of the three counts whose sum bounds the number of basic operations in Theorem 3.11; it also bounds the total increase of the potential used in Lemma 3.10.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, p. 927, Lemma 3.9

import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Run

namespace GoldbergTarjan.Generic

/-- Lemma 3.9 (Goldberg–Tarjan 1988, p. 927). The number of saturating push operations is at
most `2nm`, where `n = |V|` and `m = |E|`. -/
theorem saturating_push_count_le {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (σ : ℕ → State V) (K : ℕ) (hrun : IsRun N σ K) :
    saturatingPushCount N σ K ≤ 2 * Fintype.card V * N.numEdges := by sorry

end GoldbergTarjan.Generic
