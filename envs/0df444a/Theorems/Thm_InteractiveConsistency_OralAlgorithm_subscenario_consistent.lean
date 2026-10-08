-- Prove2me | Theorems.Thm_InteractiveConsistency_OralAlgorithm_subscenario_consistent
-- name    : InteractiveConsistency.OralAlgorithm.subscenario_consistent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:31:36.629459+00:00
-- url     : https://prove2.me/theorems/62c998db-378d-4958-9ea8-e5327f4f15fb
-- title:
--   Section 3, note after step (2) (p. 230) — σ̂(w) = σ(wq) is an m-level scenario on P − {q} consistent with N
-- statement:
--   Let $P$ be a finite set of $n$ processors, $m = m'+1\ge 1$, $N\subseteq P$ with $|N|\ge n-m$, and $\sigma$ an $(m+1)$-level scenario consistent with $N$. Let $q\in P$ be faulty, $q\notin N$. Define
--   $$\hat\sigma(w) = \sigma(wq)$$
--   for strings $w$ over $P-\{q\}$. Then $N\subseteq P-\{q\}$, $|N| \ge (n-1)-(m-1)$, and $\hat\sigma$ is an $m$-level scenario on $P-\{q\}$ consistent with $N$.
--
--   The paper notes that $\hat\sigma_p$ "corresponds to the $m$-level subscenario of $\sigma$ in which $q$ is excluded and in which each processor's private value is the value it obtains directly from $q$ in $\sigma$", and its induction hypothesis is applied to this subscenario. The restriction of $\hat\sigma$ to strings beginning with $p$ is exactly the view $w\mapsto\sigma_p(pwq)$ that the recursive call of step (2) receives.
--
--   **Formalization Note.** $\hat\sigma$ is `fun w => σ (w ++ [q])`; level $m$ means consistency on strings of length $\le m+1$ (`ConsistentUpTo (P.erase q) N (m' + 1)`). $|N|\ge (n-1)-(m-1)$ is written `(P.erase q).card ≤ N.card + m'`.
-- source:
--   Pease, Shostak & Lamport, Reaching agreement in the presence of faults, J. ACM 27 (1980), p. 230, Section 3, note after step (2); used on p. 231 (σ̂(w) = σ(wq), "By the induction hypothesis")

import Mathlib
import Definitions.Def_InteractiveConsistency_OralAlgorithm_Scenario

namespace InteractiveConsistency.OralAlgorithm

theorem subscenario_consistent {α V : Type*} [DecidableEq α] (P N : Finset α) (m' : ℕ)
    (hNP : N ⊆ P) (hN : P.card ≤ N.card + (m' + 1))
    (σ : List α → V) (hσ : ConsistentUpTo P N (m' + 2) σ)
    (q : α) (hqP : q ∈ P) (hqN : q ∉ N) :
    N ⊆ P.erase q ∧ (P.erase q).card ≤ N.card + m' ∧
      ConsistentUpTo (P.erase q) N (m' + 1) (fun w => σ (w ++ [q])) := by sorry

end InteractiveConsistency.OralAlgorithm
