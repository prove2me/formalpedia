-- Prove2me | Theorems.Thm_InteractiveConsistency_OralAlgorithm_record_of_nonfaulty
-- name    : InteractiveConsistency.OralAlgorithm.record_of_nonfaulty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:36:20.713778+00:00
-- url     : https://prove2.me/theorems/79cd7f29-153a-42e4-add6-1ba5e7790322
-- title:
--   Section 3, Induction Step ¶1 (p. 231) — for nonfaulty p, q, step (1) succeeds and p records σ(q)
-- statement:
--   Let $P$ be a finite set of $n$ processors, $m\ge 0$ with $n\ge 3m+1$, $N\subseteq P$ a set of nonfaulty processors with $|N|\ge n-m$, and $\sigma$ an $(m+1)$-level scenario consistent with $N$. For all nonfaulty $p, q\in N$, the condition of step (1) of the Section 3 procedure holds for $p$'s view $\sigma_p$ and the processor $q$, and
--   $$\mathrm{record}(m, P, \sigma_p, q) = \sigma(q) = V_q .$$
--
--   This is clause (i) of interactive consistency. The paper argues it at the start of the induction step: the set of nonfaulty processors has $n-m > (n+m)/2$ members and every relay chain through it reproduces $V_q$, so it qualifies as $Q$ in step (1).
--
--   **Formalization Note.** The paper writes this inside the induction step ($m>0$) and the basis $m=0$ separately; the statement covers every $m\ge 0$. The paper's "p records $V_q$ and $q$" is a printed slip for "records $V_q$ for $q$". The view of $p$ is `fun w => σ (p :: w)` and the recorded value is `some (σ [q])`.
-- source:
--   Pease, Shostak & Lamport, Reaching agreement in the presence of faults, J. ACM 27 (1980), p. 231, Section 3, Basis and Induction Step ¶1

import Mathlib
import Definitions.Def_InteractiveConsistency_OralAlgorithm_Scenario
import Definitions.Def_InteractiveConsistency_OralAlgorithm_Procedure

namespace InteractiveConsistency.OralAlgorithm

theorem record_of_nonfaulty {α V : Type*} [DecidableEq α] (P N : Finset α) (m : ℕ)
    (hn : 3 * m + 1 ≤ P.card) (hNP : N ⊆ P) (hN : P.card ≤ N.card + m)
    (σ : List α → V) (hσ : ConsistentUpTo P N (m + 1) σ)
    (p q : α) (hp : p ∈ N) (hq : q ∈ N) :
    StepOne m P (fun w => σ (p :: w)) q ∧
      record m P (fun w => σ (p :: w)) q = some (σ [q]) := by sorry

end InteractiveConsistency.OralAlgorithm
