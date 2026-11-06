-- Prove2me | Theorems.Thm_ImpatientQPTAS_greedy_true_process
-- name    : ImpatientQPTAS.greedy_true_process
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:59:44.46819+00:00
-- url     : https://prove2.me/theorems/56bb02b3-3884-4b9e-a328-1d59ee5d78f6
-- title:
--   §2.5, pp.12–13 — greedy for the rounded-up values in the true process (repaired)
-- statement:
--   Let $B$ be a set of customers, with $0\le r'_i\le r_i$ and $0\le p_i\le p'_i\le1$ on $B$. Let $G$ be a policy that, on every nonempty $A\subseteq B$ and at every stage, serves a maximizer of the recursion of the optimal value $V^{(r',p')}$. Then for every $A\subseteq B$,
--   $$
--   V^{(r',p')}(A)\le R^{(r,p)}_A(G).
--   $$
--
--   So an optimal rule for the rounded data, played in the true process, earns at least its rounded value, and it is a deterministic function of the state.
--
--   Differences from the source:
--   - reading: "We then utilize Theorem 2.7, producing an adaptive service policy S̃"; the construction of App. A.6 flips coins and keeps an eliminated set → S̃ plays greedily for V↑ in the true process; reason: Theorem 1.1 promises a deterministic algorithm and §1.1 a function of the state; the inequality R^(p)(S̃) ≥ R^(p↑)(S↑*) of p.13 holds for this S̃
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, §2.5, pp.12–13; App. A.6

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model

namespace ImpatientQPTAS

/-- Segev, arXiv:2209.13878v1, §2.5, pp.12–13, repaired: acting greedily for the rounded-up values in
the true process earns at least those values. If `p ≤ p'` and `0 ≤ r' ≤ r` on `B`, and `G` serves a
maximizer of the recursion of `V r' p'` on every nonempty subset of `B`, then
`V r' p' A ≤ R^(r,p)_G(A)` for every `A ⊆ B`.

**Formalization Note.** This replaces the use of Theorem 2.7 in "We then utilize Theorem 2.7, producing an
adaptive service policy S̃": the construction of Appendix A.6 flips coins and keeps an eliminated set,
while Theorem 1.1 promises a deterministic algorithm and §1.1 a function of the state. -/
theorem greedy_true_process {n : ℕ} (r r' p p' : Fin n → ℝ) (B : Finset (Fin n))
    (hr : ∀ i ∈ B, 0 ≤ r' i ∧ r' i ≤ r i) (hp : ∀ i ∈ B, 0 ≤ p i ∧ p i ≤ p' i ∧ p' i ≤ 1)
    (G : Policy n)
    (hG : ∀ t A, A ⊆ B → A.Nonempty →
      ∃ i ∈ A, G t A = some i ∧ r' i + thin p' (A.erase i) (V r' p') = V r' p' A) :
    ∀ A, A ⊆ B → V r' p' A ≤ (⟨r, p⟩ : Instance n).Rfrom G A := by sorry

end ImpatientQPTAS
