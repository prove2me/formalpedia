-- Prove2me | Theorems.Thm_InteractiveConsistency_Authenticated_faulty_origin_set_subset
-- name    : InteractiveConsistency.Authenticated.faulty_origin_set_subset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:40:26.559007+00:00
-- url     : https://prove2.me/theorems/4d3dac37-a9dd-420a-8620-7ba17614a0ad
-- title:
--   Section 5 — a faulty originator's reports transfer between nonfaulty receivers
-- statement:
--   Let $P$ be a finite set of processors with $m\le|P|$, and let $N\subseteq P$ satisfy $|P|\le|N|+m$. Let $\sigma$ be an authenticated $(m+1)$-level scenario consistent with $N$, with non-NIL private values. If $p,p'\in N$ are nonfaulty and $q\in P\setminus N$ is faulty, then
--
--   $$
--   S_{pq}\subseteq S_{p'q}.
--   $$
--
--   The inclusion is valid for every ordered pair of nonfaulty receivers. Applying it with their roles exchanged gives equality of the two sets, which supplies agreement for a faulty originator.
--
--   **Formalization Note** Each set uses only its named receiver's own view. The bound on the number of faulty processors includes $q$, and the relay strings have distinct letters, avoid the receiver and originator, and have length at most $m$.
-- source:
--   Pease, Shostak & Lamport, Reaching agreement in the presence of faults, J. ACM 27 (1980), p. 234, Section 5 proof paragraph; https://doi.org/10.1145/322186.322188

import Mathlib
import Definitions.Def_InteractiveConsistency_Authenticated_Procedure
set_option autoImplicit false

namespace InteractiveConsistency.Authenticated

/-- Section 5, p. 234: for a faulty originator, every non-NIL report seen by
one nonfaulty receiver is also seen by every other nonfaulty receiver. -/
theorem faulty_origin_set_subset {α V : Type*} [DecidableEq α]
    (P N : Finset α) (m : ℕ) (σ : List α → Option V)
    (hmn : m ≤ P.card) (hN : N ⊆ P) (hcount : P.card ≤ N.card + m)
    (hscenario : IsAuthScenario P σ)
    (hconsistent : AuthConsistent P N m σ)
    (p p' q : α) (hp : p ∈ N) (hp' : p' ∈ N)
    (hqP : q ∈ P) (hqN : q ∉ N) :
    S m P (view σ p) p q ⊆ S m P (view σ p') p' q := by sorry

end InteractiveConsistency.Authenticated
