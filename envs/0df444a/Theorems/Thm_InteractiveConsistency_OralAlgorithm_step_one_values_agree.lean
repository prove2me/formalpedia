-- Prove2me | Theorems.Thm_InteractiveConsistency_OralAlgorithm_step_one_values_agree
-- name    : InteractiveConsistency.OralAlgorithm.step_one_values_agree
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:31:10.783986+00:00
-- url     : https://prove2.me/theorems/3c72f4a9-e64f-4369-8583-8c4f4ca4c673
-- title:
--   Section 3, Induction Step ¶3 (p. 231) — two step-(1) quorums give the same value
-- statement:
--   Let $P$ be a finite set of $n$ processors, $N\subseteq P$ with $|N|\ge n-m$, and $\sigma$ an $(m+1)$-level scenario consistent with $N$. Let $p, p'\in N$ be nonfaulty and $q\in P$. Suppose $Q_1, Q_2\subseteq P$ both have more than $(n+m)/2$ members, and $v, v'\in V$ satisfy
--   $$\sigma(p\,w\,q) = v \text{ for every string } w \text{ over } Q_1 \text{ with } |w|\le m,\qquad \sigma(p'\,w\,q) = v' \text{ for every string } w \text{ over } Q_2 \text{ with } |w|\le m .$$
--   Then $v = v'$.
--
--   This is the case of the paper's proof in which both $p$ and $p'$ exit the procedure at step (1): the two quorums share more than $m$ members, one of them nonfaulty, so both quorums yield the same value.
--
--   **Formalization Note.** $\sigma(p\,w\,q)$ is `σ (p :: (w ++ [q]))`, i.e. $\sigma_p(pwq)$. "More than $(n+m)/2$ members" is `P.card + m < 2 * Qᵢ.card`. The hypothesis $n\ge 3m+1$ of Section 3 is not needed for this step and is omitted, which makes the statement stronger.
-- source:
--   Pease, Shostak & Lamport, Reaching agreement in the presence of faults, J. ACM 27 (1980), p. 231, Section 3, Induction Step ¶3

import Mathlib
import Definitions.Def_InteractiveConsistency_OralAlgorithm_Scenario

namespace InteractiveConsistency.OralAlgorithm

theorem step_one_values_agree {α V : Type*} [DecidableEq α] (P N : Finset α) (m : ℕ)
    (hNP : N ⊆ P) (hN : P.card ≤ N.card + m)
    (σ : List α → V) (hσ : ConsistentUpTo P N (m + 1) σ)
    (p p' q : α) (hp : p ∈ N) (hp' : p' ∈ N) (hq : q ∈ P)
    (Q₁ Q₂ : Finset α) (hQ₁ : Q₁ ⊆ P) (hQ₂ : Q₂ ⊆ P)
    (hQ₁card : P.card + m < 2 * Q₁.card) (hQ₂card : P.card + m < 2 * Q₂.card)
    (v v' : V)
    (hv : ∀ w : List α, IsStringOver Q₁ w → w.length ≤ m → σ (p :: (w ++ [q])) = v)
    (hv' : ∀ w : List α, IsStringOver Q₂ w → w.length ≤ m → σ (p' :: (w ++ [q])) = v') :
    v = v' := by sorry

end InteractiveConsistency.OralAlgorithm
