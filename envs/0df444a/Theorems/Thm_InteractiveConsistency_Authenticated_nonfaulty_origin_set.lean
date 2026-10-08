-- Prove2me | Theorems.Thm_InteractiveConsistency_Authenticated_nonfaulty_origin_set
-- name    : InteractiveConsistency.Authenticated.nonfaulty_origin_set
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:40:06.934254+00:00
-- url     : https://prove2.me/theorems/02e17596-2567-430d-9719-5bd314af173f
-- title:
--   Section 5 — a nonfaulty originator yields a singleton S_pq
-- statement:
--   Let $P$ be a finite set of processors, $N\subseteq P$ the nonfaulty set, and $m\le|P|$ an upper bound on the number of faults, so that $|P|\le |N|+m$. Let $\sigma$ be an authenticated $(m+1)$-level scenario consistent with $N$, with non-NIL private values. For nonfaulty processors $p,q\in N$, the originator $q$ has a private value $v\in V$ and
--
--   $$
--   \sigma(q)=v,\qquad S_{pq}=\{v\}.
--   $$
--
--   This identifies the set from which receiver $p$ makes its decision when the originator is nonfaulty, including the case $p=q$.
--
--   **Formalization Note** The set is computed from $p$'s view $w\mapsto\sigma(pw)$, with intermediate strings of distinct processors of length at most $m$. The theorem makes the paper's actual private value explicit by asserting $\sigma(q)=v$, rather than treating NIL as a possible private value.
-- source:
--   Pease, Shostak & Lamport, Reaching agreement in the presence of faults, J. ACM 27 (1980), p. 233, Section 5 final paragraph; https://doi.org/10.1145/322186.322188

import Mathlib
import Definitions.Def_InteractiveConsistency_Authenticated_Procedure
set_option autoImplicit false

namespace InteractiveConsistency.Authenticated

/-- Section 5, p. 233: a nonfaulty originator's value is the sole non-NIL
value visible in the receiver's set. -/
theorem nonfaulty_origin_set {α V : Type*} [DecidableEq α]
    (P N : Finset α) (m : ℕ) (σ : List α → Option V)
    (hmn : m ≤ P.card) (hN : N ⊆ P) (hcount : P.card ≤ N.card + m)
    (hscenario : IsAuthScenario P σ)
    (hconsistent : AuthConsistent P N m σ)
    (p q : α) (hp : p ∈ N) (hq : q ∈ N) :
    ∃ v : V, σ [q] = some v ∧ S m P (view σ p) p q = {v} := by sorry

end InteractiveConsistency.Authenticated
