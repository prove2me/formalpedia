-- Prove2me | Theorems.Thm_NegNetQueue_Meets_eq_2_one_step
-- name    : NegNetQueue.Meets.eq_2_one_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:19.538457+00:00
-- url     : https://prove2.me/theorems/1edc3b55-0c0c-4c33-aa0b-fdd559158ce9
-- title:
--   §4, p. 9, (2) — row k of A is the law of the queue size at the next service completion
-- statement:
--   Let $\varepsilon$ be an event sequence of an M/M/c/n queue ($\lambda,\mu>0$, $c\ge1$, all servers busy), and let $q=c\mu/(\lambda+c\mu)$. Consider a queue of current size $k$ with $1\le k\le n$, and let $L$ be the queue size right after the next service completion. Then for every $i\in\{0,\dots,n\}$,
--   $$P(L=i)=A(k,i),$$
--   where $A$ is the matrix of (2). In particular state $n$ moves to $n-1$ with probability $1$, and state $1$ is the only state that leads to $0$ with positive probability.
--
--   This is the one-step law that makes $A$ the transition matrix of the queue size at consecutive service completions, the basis of Theorem 2.
--
--   **Formalization Note.** $L$ is expressed with a tagged customer at the head of the queue (position $1$ of a queue of length $k$): she enters service exactly at the next completion, so $L$ is the queue length at her entry, `lenAtEntry n 1 k`. The row index $k$ is the element $\langle k,\cdot\rangle$ of $\{0,\dots,n\}$.
-- source:
--   Hassin, Meilijson & Perlman, Queueing with Negative Network Effects, SSRN 4097977 (version of July 2, 2022), p. 9, §4, display (2) and the paragraph before it

import Mathlib
import Definitions.Def_NegNetQueue_Meets_EventSeq
import Definitions.Def_NegNetQueue_Meets_Model

namespace NegNetQueue.Meets

open MeasureTheory ProbabilityTheory

/-- (2), p. 9: from queue size `k` (`1 ≤ k ≤ n`), the queue size at the next service completion
has law row `k` of `A`. The customer at the head of the queue (position 1) enters service at that
completion, so this queue size is `lenAtEntry n 1 k`. -/
theorem eq_2_one_step {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (lam mu : ℝ) (c : ℕ)
    (hlam : 0 < lam) (hmu : 0 < mu) (hc : 1 ≤ c) (ε : ℕ → Ω → Bool)
    (hε : IsEventSeq P lam mu c ε) (n : ℕ) :
    ∀ (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin (n + 1)),
      (P {ω | lenAtEntry n 1 k ε ω = ((i : ℕ) : ℕ∞)}).toReal =
        Amat n (qComp lam mu c) ⟨k, Nat.lt_succ_of_le hkn⟩ i := by sorry

end NegNetQueue.Meets
