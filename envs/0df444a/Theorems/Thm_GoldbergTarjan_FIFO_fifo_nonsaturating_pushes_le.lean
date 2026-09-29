-- Prove2me | Theorems.Thm_GoldbergTarjan_FIFO_fifo_nonsaturating_pushes_le
-- name    : GoldbergTarjan.FIFO.fifo_nonsaturating_pushes_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:37:32.791978+00:00
-- url     : https://prove2.me/theorems/2b330157-ae24-4702-8696-bed3dc57c66a
-- title:
--   Corollary 4.4 — the first-in, first-out push-relabel algorithm makes at most $4n^3$ nonsaturating pushes
-- statement:
--   Let $G$ be a flow network with $n = |V|$ vertices, capacities $c \ge 0$, no loops, and source $s \neq t$. Fix edge lists in any order and an initial queue order. Consider any run of the first-in, first-out algorithm: start from the initial preflow that saturates the edges leaving $s$, the labeling $d(s) = n$, $d(v) = 0$ otherwise, and the queue of vertices $v \notin \{s,t\}$ with $c(s,v) > 0$, then apply the discharge operation of Fig. 4 repeatedly. Then the number of nonsaturating pushes performed is at most
--   $$4n^3.$$
--
--   Together with the $O(nm)$ bound on the remaining work of the implementation, this gives the $O(n^3)$ running time of the FIFO algorithm (Theorem 4.5). That bound matches Karzanov's algorithm and improves on the $O(n^2 m)$ bound on nonsaturating pushes of the generic method.
--
--   **Formalization Note** The bound is stated for every run of any finite number $K$ of discharges, so it applies to the whole execution and to every prefix of it. Nonsaturating pushes are counted over all push/relabel operations inside all discharges.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, p. 931, Corollary 4.4

import Mathlib
import Definitions.Def_GoldbergTarjan_FIFO_Network
import Definitions.Def_GoldbergTarjan_FIFO_PushRelabel
import Definitions.Def_GoldbergTarjan_FIFO_Algorithm
import Definitions.Def_GoldbergTarjan_FIFO_Counts

namespace GoldbergTarjan.FIFO

/-- Corollary 4.4 (Goldberg–Tarjan 1988, p. 931): the number of nonsaturating pushes during the
first-in, first-out algorithm is at most `4n³`, where `n = |V|`. Stated for every network,
every edge list order, every initial queue order and every run of `K` discharge operations
(Fig. 4) from the initialization of Fig. 2 with the simple labeling. -/
theorem fifo_nonsaturating_pushes_le {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (L : V → List V) (K : ℕ) (S : ℕ → State V) (J : ℕ → ℕ)
    (hrun : IsFIFORun N L K S J) :
    nonsatPushCount N L K S J ≤ 4 * Fintype.card V ^ 3 := by sorry

end GoldbergTarjan.FIFO
