-- Prove2me | Theorems.Thm_GoldbergTarjan_Generic_nonsaturating_push_count_le
-- name    : GoldbergTarjan.Generic.nonsaturating_push_count_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:30:42.898679+00:00
-- url     : https://prove2.me/theorems/b969c861-d500-4a32-90d7-0f547781b047
-- title:
--   Lemma 3.10 — at most $4n^2m$ nonsaturating pushes (with $m \ge n - 1$)
-- statement:
--   Let $N$ be a flow network with $n$ vertices and $m$ edges, satisfying the standing assumption $m \ge n - 1$ of §2, and let $(f_0,d_0), \dots, (f_K,d_K)$ be an execution of the generic algorithm, started from the initial state of Fig. 2 with the simple labeling. Then the number of nonsaturating pushes among its $K$ steps (pushes Push$(v,w)$ after which $r_f(v,w) > 0$) satisfies
--
--   $$\#\{\text{nonsaturating pushes}\} \le 4n^2 m.$$
--
--   This is the dominant term of the operation count of Theorem 3.11.
--
--   **Formalization Note.** The paper states $m \ge n-1$ once, at the start of §2, "for ease in stating time bounds"; its proof of Lemma 3.10 uses it in the last inequality, so it is a hypothesis here.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, p. 928, Lemma 3.10 (standing assumption m ≥ n − 1 from p. 923)

import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Run

namespace GoldbergTarjan.Generic

/-- Lemma 3.10 (Goldberg–Tarjan 1988, p. 928). Under the standing assumption `m ≥ n - 1`
(§2, p. 923), the number of nonsaturating pushing operations is at most `4n²m`, where
`n = |V|` and `m = |E|`. -/
theorem nonsaturating_push_count_le {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hm : Fintype.card V - 1 ≤ N.numEdges)
    (σ : ℕ → State V) (K : ℕ) (hrun : IsRun N σ K) :
    nonsaturatingPushCount N σ K ≤ 4 * Fintype.card V ^ 2 * N.numEdges := by sorry

end GoldbergTarjan.Generic
