-- Prove2me | Theorems.Thm_InteractiveConsistency_Authenticated_signed_procedure_assures_ic
-- name    : InteractiveConsistency.Authenticated.signed_procedure_assures_ic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:40:22.478888+00:00
-- url     : https://prove2.me/theorems/ae344342-0625-4e08-9473-922039f4ae2b
-- title:
--   Section 5 — the authenticated S_pq procedure assures interactive consistency for n ≥ m
-- statement:
--   Let $P$ be a finite set of $n$ processors, let $V$ be a set of private values, and let $m\le n$. For every nonfaulty set $N\subseteq P$ with $|N|\ge n-m$ and every authenticated $(m+1)$-level scenario $\sigma$ consistent with $N$, assume that every processor has a non-NIL private value. Processor $p$ applies the singleton-set procedure to its own view $w\mapsto\sigma(pw)$ and records an optional value $R_p(q)$ for each $q\in P$. Then
--
--   $$
--   R_p(q)=\sigma(q)\quad(p,q\in N),\qquad
--   R_p(r)=R_{p'}(r)\quad(p,p'\in N,\ r\in P).
--   $$
--
--   Thus every nonfaulty processor records the actual private value of each nonfaulty originator, and all nonfaulty processors produce the same vector, including the entries for faulty originators.
--
--   **Formalization Note** The printed $n\ge m$ condition is retained. The theorem quantifies over every admissible $N$; the procedure receives neither $N$ nor the full scenario. Strings are bounded to those inspected by the $(m+1)$-level procedure. NIL is represented by `none`, and the source's private values are required to be non-NIL. The authenticator's cryptographic construction and its probability guarantee are outside this theorem.
-- source:
--   Pease, Shostak & Lamport, Reaching agreement in the presence of faults, J. ACM 27 (1980), pp. 233–234, Section 5 procedure and Q.E.D.; interactive-consistency clauses, p. 232; https://doi.org/10.1145/322186.322188

import Mathlib
import Definitions.Def_InteractiveConsistency_Authenticated_Procedure
set_option autoImplicit false

namespace InteractiveConsistency.Authenticated

/-- Section 5, pp. 233–234: the authenticated-message procedure assures
interactive consistency for every `n ≥ m`. -/
theorem signed_procedure_assures_ic {α V : Type*} [DecidableEq α]
    (P : Finset α) (m : ℕ) (hmn : m ≤ P.card) :
    ∀ N : Finset α, N ⊆ P → P.card ≤ N.card + m →
    ∀ σ : List α → Option V,
      IsAuthScenario P σ → AuthConsistent P N m σ →
      (∀ p ∈ N, ∀ q ∈ N, record m P (view σ p) p q = σ [q]) ∧
      (∀ p ∈ N, ∀ p' ∈ N, ∀ r ∈ P,
        record m P (view σ p) p r = record m P (view σ p') p' r) := by sorry

end InteractiveConsistency.Authenticated
