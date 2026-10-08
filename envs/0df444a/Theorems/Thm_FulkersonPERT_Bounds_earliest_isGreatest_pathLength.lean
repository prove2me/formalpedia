-- Prove2me | Theorems.Thm_FulkersonPERT_Bounds_earliest_isGreatest_pathLength
-- name    : FulkersonPERT.Bounds.earliest_isGreatest_pathLength
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:22:07.412982+00:00
-- url     : https://prove2.me/theorems/48b9dd5a-201a-4bd9-b7ca-1fcde0c989fc
-- title:
--   §4, p. 11 with (3.6) — the earliest-time recursion is the length of a longest path from the origin
-- statement:
--   Let $N$ be a project network with events $0,\dots,n$ and let $y_{ab}\in\mathbb R$ be arbitrary arc lengths. For an event $i$, let $\ell_i$ be given by the recursion $\ell_0=0$ and
--   $$\ell_j=\max_{(i,j)\in N}\bigl(\ell_i+y_{ij}\bigr)\qquad(j\ne 0).$$
--   Then $\ell_i$ is the greatest length of a path from the origin to $i$: it is the length of some path from $0$ to $i$, and every path from $0$ to $i$ has length at most $\ell_i$.
--
--   Fulkerson defines $\ell_i(t)$ in (3.6) as "the length of a longest or critical path from node 1 to node i", and uses the recursion $\ell_{i+1}(t_C)=\max[\ell_1(t_A)+t_1,\dots,\ell_i(t_A)+t_i]$ in the proof of (4.4) on p. 11. This statement identifies the two.
--
--   **Formalization Note** Fulkerson's node $i$ is event $i-1$. Paths are lists of events starting at $0$ and ending at $i$, consecutive events joined by arcs; the path consisting of the origin alone has length $0$. Arc lengths may be negative.
-- source:
--   Fulkerson, Expected Critical Path Lengths in PERT Networks, RAND Memorandum RM-3075-PR (1962), p. 5, (3.6); p. 11, §4, proof of (4.4), display before (4.11)

import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes
import Definitions.Def_FulkersonPERT_Bounds_Model

namespace FulkersonPERT.Bounds
open CriticalPath.Events
theorem earliest_isGreatest_pathLength {n : ℕ} (N : ProjectNetwork n)
    (y : Fin (n + 1) → Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    IsGreatest {L : ℝ | ∃ p : List (Fin (n + 1)), IsPathTo N p i ∧ L = pathLength y p}
      (earliest N y i) := by sorry
end FulkersonPERT.Bounds
