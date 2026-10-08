-- Prove2me | Theorems.Thm_FulkersonPERT_Bounds_earliest_eq_of_eqOn_bundles
-- name    : FulkersonPERT.Bounds.earliest_eq_of_eqOn_bundles
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:22:17.104562+00:00
-- url     : https://prove2.me/theorems/07bbd19c-e055-48a0-9ab9-e382db9966af
-- title:
--   §3, p. 6 — ℓ_i(t) does not depend on the arcs of the bundles B_{i+1}, …, B_n
-- statement:
--   Let $N$ be a project network with events $0,\dots,n$, let $i$ be an event, and let $y$ and $y'$ be two assignments of real lengths to the arcs. Suppose $y_{ab}=y'_{ab}$ for every arc $(a,b)$ with $b\le i$, that is, on the bundles $B_0,\dots,B_i$. Then the critical path lengths to $i$ agree:
--   $$\ell_i(y)=\ell_i(y').$$
--
--   This is Fulkerson's observation on p. 6 that $\ell_i(t)$ "does not depend on the values assigned to arcs of the bundles $B_{i+1},\dots,B_n$", which lets the expected length $e_i$ be written as the sum (3.9) over the arcs of $B_1\cup\dots\cup B_i$ only.
--
--   **Formalization Note** Fulkerson's node $i$ is event $i-1$; $\ell_i$ is the earliest-event-time recursion of the referenced network definitions.
-- source:
--   Fulkerson, Expected Critical Path Lengths in PERT Networks, RAND Memorandum RM-3075-PR (1962), p. 6, §3, observation before (3.8)–(3.11)

import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes
import Definitions.Def_FulkersonPERT_Bounds_Model

namespace FulkersonPERT.Bounds
open CriticalPath.Events
theorem earliest_eq_of_eqOn_bundles {n : ℕ} (N : ProjectNetwork n)
    (y y' : Fin (n + 1) → Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (h : ∀ a b, (a, b) ∈ N.P → b ≤ i → y a b = y' a b) :
    earliest N y i = earliest N y' i := by sorry
end FulkersonPERT.Bounds
