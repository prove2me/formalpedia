-- Prove2me | Theorems.Thm_FulkersonPERT_Bounds_expected_critical_path_bounds
-- name    : FulkersonPERT.Bounds.expected_critical_path_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:34:30.280999+00:00
-- url     : https://prove2.me/theorems/28437985-62f1-49b7-a2a2-48e5bb3e929e
-- title:
--   (4.4), p. 10 — g_i ≤ f_i ≤ e_i for every node of a PERT network with bundle-independent arc lengths
-- statement:
--   Let $N$ be a PERT network with events $0,\dots,n$: origin $0$, terminal $n$, every arc $(i,j)$ with $i<j$, and every event on a path from origin to terminal. For every event $j$ let the lengths of the arcs entering $j$ (the bundle $B_j$) have a finite joint distribution $p_j$ on a finite set $S_j$ of bundle vectors, the distributions of distinct bundles being independent. Let
--
--   1. $e_i=\sum_t p(t)\,\ell_i(t)$ be the expected length of a critical path to $i$, where $p(t)=\prod_j p_j(t_{B_j})$ and $\ell_i(t)$ is the longest-path length from the origin to $i$ under the arc lengths $t$ (3.7);
--   2. $g_i$ be the critical path length to $i$ when every arc has its expected length $\bar t_{ij}=\sum_{v\in S_j}p_j(v)v_i$ (3.13);
--   3. $f_0=0$ and $f_j=\sum_{v\in S_j}p_j(v)\max_{(i,j)\in N}(f_i+v_i)$ for $j\neq0$ (4.2).
--
--   Then for every event $i$,
--   $$g_i\;\le\;f_i\;\le\;e_i .$$
--
--   The mean-length estimate $g_i$, the classical PERT figure, is thus a lower bound for the expected project duration, and Fulkerson's numbers $f_i$, computable bundle by bundle, are a lower bound that is at least as good.
--
--   **Formalization Note** Fulkerson's node $i$ is event $i-1$, so his $i=1,\dots,n$ ranges over all events. The maximum over missing arcs is ignored (`Finset.sup'` over the arcs that exist). There is one arc per ordered pair of events. Arc lengths may be negative: the page assumes nonnegativity but its footnote on p. 4 says this is not essential in §3–§4, so the statement is the more general one. The referenced project network requires origin and terminal to be distinct ($n\ge1$).
-- source:
--   Fulkerson, Expected Critical Path Lengths in PERT Networks, RAND Memorandum RM-3075-PR (1962), p. 10, (4.4)

import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes
import Definitions.Def_FulkersonPERT_Bounds_Model

namespace FulkersonPERT.Bounds
open CriticalPath.Events
theorem expected_critical_path_bounds {n : ℕ} (N : ProjectNetwork n) (D : BundleDist n)
    (hD : D.IsProb) :
    ∀ i : Fin (n + 1), meanCPL N D i ≤ fNum N D i ∧ fNum N D i ≤ expectedLength N D i := by sorry
end FulkersonPERT.Bounds
