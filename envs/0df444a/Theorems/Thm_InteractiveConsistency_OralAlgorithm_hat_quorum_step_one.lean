-- Prove2me | Theorems.Thm_InteractiveConsistency_OralAlgorithm_hat_quorum_step_one
-- name    : InteractiveConsistency.OralAlgorithm.hat_quorum_step_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:31:25.519772+00:00
-- url     : https://prove2.me/theorems/f05f8b36-3900-43a3-b694-0a31755246d3
-- title:
--   Section 3, Induction Step ¶4 (p. 231) — Q̂ = Q − {q} has ≥ ⌊(n+m)/2⌋ members and satisfies step (1) of the recursive call
-- statement:
--   Let $P$ be a finite set of $n$ processors, $m = m'+1\ge 1$, $q\in P$, and $p'$ a processor. Suppose $Q\subseteq P$ has more than $(n+m)/2$ members and $v\in V$ satisfies $\sigma(p'\,w\,q) = v$ for every string $w$ over $Q$ with $|w|\le m$ (so $Q$ and $v$ satisfy step (1) for $p'$ and $q$). Let $\hat Q = Q-\{q\}$. Then
--   1. $\hat Q \subseteq P-\{q\}$;
--   2. $|\hat Q| \ge \lfloor (n+m)/2\rfloor$;
--   3. $|\hat Q| > \bigl[(n-1)+(m-1)\bigr]/2$;
--   4. for every $q'\in\hat Q$ and every string $w$ over $\hat Q$ with $|w|\le m-1$,
--   $$\hat\sigma_{p'}(p'\,w\,q') = \sigma_{p'}(p'\,w\,q'\,q) = v .$$
--
--   Items 1, 3 and 4 say that $\hat Q$ and $v$ satisfy step (1) of the recursive call (for $m-1$ faults, processor set $P-\{q\}$, view $\hat\sigma_{p'}$) for every target $q'\in\hat Q$; item 2 is the count step (2) needs. In the paper's proof this is the parenthetical remark that settles the case where $p'$ exits at step (1) and $p$ executes step (2).
--
--   **Formalization Note.** The page prints "$\sigma_{p'}(p'wq') = \sigma_{p'}(p'wq'q)$"; the first $\sigma_{p'}$ is a printed slip for $\hat\sigma_{p'}$, and the statement uses $\hat\sigma(u) = \sigma(uq)$ directly: item 4 is `σ (p' :: ((w ++ [q']) ++ [q])) = v`. $\lfloor (n+m)/2\rfloor$ is `(P.card + (m' + 1)) / 2` and item 3 is `(P.erase q).card + m' < 2 * (Q.erase q).card`.
-- source:
--   Pease, Shostak & Lamport, Reaching agreement in the presence of faults, J. ACM 27 (1980), p. 231, Section 3, Induction Step ¶4 (the parenthesis)

import Mathlib
import Definitions.Def_InteractiveConsistency_OralAlgorithm_Scenario

namespace InteractiveConsistency.OralAlgorithm

theorem hat_quorum_step_one {α V : Type*} [DecidableEq α] (P : Finset α) (m' : ℕ)
    (σ : List α → V) (p' q : α) (hqP : q ∈ P)
    (Q : Finset α) (hQP : Q ⊆ P) (hQcard : P.card + (m' + 1) < 2 * Q.card) (v : V)
    (hv : ∀ w : List α, IsStringOver Q w → w.length ≤ m' + 1 → σ (p' :: (w ++ [q])) = v) :
    Q.erase q ⊆ P.erase q ∧
      (P.card + (m' + 1)) / 2 ≤ (Q.erase q).card ∧
      (P.erase q).card + m' < 2 * (Q.erase q).card ∧
      ∀ q' ∈ Q.erase q, ∀ w : List α, IsStringOver (Q.erase q) w → w.length ≤ m' →
        σ (p' :: ((w ++ [q']) ++ [q])) = v := by sorry

end InteractiveConsistency.OralAlgorithm
