-- Prove2me | Theorems.Thm_NegNetQueue_Meets_theorem_2_2
-- name    : NegNetQueue.Meets.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:24.167334+00:00
-- url     : https://prove2.me/theorems/92c6d667-1e87-4450-ac45-91b1f83be6cb
-- title:
--   Theorem 2 (2), p. 10 (corrected) — after j ≤ k service completions the queue size has law row k of A^j
-- statement:
--   Let $\varepsilon$ be an event sequence of an M/M/c/n queue and $q=c\mu/(\lambda+c\mu)$. Consider a customer in position $j$ of a queue of current length $k$, with $1\le j\le k\le n$. She enters service at the $j$-th service completion. Let $L_{j,k}$ be the queue length at that moment, and $X_{j,k}$ the number of additional customers she meets until then. Then
--   1. for every $i\in\{0,\dots,n\}$,
--   $$P(L_{j,k}=i)=(A^j)(k,i);$$
--   2. for every $x\ge 0$,
--   $$P(X_{j,k}=x)=\begin{cases}(A^j)(k,\,k-j+x) & k-j+x\le n,\\ 0 & \text{otherwise.}\end{cases}$$
--
--   Part 1 is the paper's statement that $A^j$ is the transition matrix from the initial queue size to the queue size after $j$ service completions (p. 9). Part 2 is Theorem 2 (2) in corrected form: the $k-j$ customers already behind her are still waiting when she enters service, so $L_{j,k}=k-j+X_{j,k}$.
--
--   **Formalization Note.** The printed Theorem 2 (2) says that the number of additional customers met is distributed as the $k$-th row of $A^j$. That row is the law of the queue length at entry; the number of new arrivals met is that row shifted by $k-j$. For $n=3$, $j=1$, $k=2$: she meets $0$ new customers with probability $q$ and $1$ with probability $1-q$, while row $2$ of $A$ puts $q$ on $1$ and $1-q$ on $2$. Both the queue-length form and the corrected count form are stated; at $k=j$ they coincide with Theorem 2 (1).
-- source:
--   Hassin, Meilijson & Perlman, Queueing with Negative Network Effects, SSRN 4097977 (version of July 2, 2022), p. 9 (§4, 'Since A is the Markov transition matrix … Aj is the transition matrix from the initial queue size to queue size after j service completions') and p. 10, Theorem 2 (2)

import Mathlib
import Definitions.Def_NegNetQueue_Meets_EventSeq
import Definitions.Def_NegNetQueue_Meets_Model

namespace NegNetQueue.Meets

open MeasureTheory ProbabilityTheory

/-- Theorem 2 (2), p. 10, in corrected form: for a customer in position `j` of a queue of current
length `k ≥ j`, the queue length when she enters service (after `j` service completions) has law
row `k` of `A^j`; equivalently the number `X_{j,k}` of additional customers she meets has law
row `k` of `A^j` shifted by the `k - j` customers already behind her. -/
theorem theorem_2_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (lam mu : ℝ) (c : ℕ)
    (hlam : 0 < lam) (hmu : 0 < mu) (hc : 1 ≤ c) (ε : ℕ → Ω → Bool)
    (hε : IsEventSeq P lam mu c ε) (n : ℕ) :
    ∀ (j k : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) (hkn : k ≤ n),
      (∀ i : Fin (n + 1),
        (P {ω | lenAtEntry n j k ε ω = ((i : ℕ) : ℕ∞)}).toReal =
          (Amat n (qComp lam mu c) ^ j) ⟨k, Nat.lt_succ_of_le hkn⟩ i) ∧
      (∀ x : ℕ,
        (P {ω | XmetAt n j k ε ω = (x : ℕ∞)}).toReal =
          if h : k - j + x ≤ n then
            (Amat n (qComp lam mu c) ^ j) ⟨k, Nat.lt_succ_of_le hkn⟩ ⟨k - j + x, Nat.lt_succ_of_le h⟩
          else 0) := by sorry

end NegNetQueue.Meets
