-- Prove2me | Theorems.Thm_KUMultimodular_lifted_value_lt_primorial
-- name    : KUMultimodular.lifted_value_lt_primorial
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:00:53.014109+00:00
-- url     : https://prove2.me/theorems/09e9a098-53b4-4050-8653-f0043227c514
-- title:
--   Proof of Theorem 4.2: $0 \le \tilde f(\tilde\alpha_i) \le d^m(r-1)^{md} < p_1\cdots p_k$ (corrected: $\max 2$ in $\ell$, $m \ge 1$)
-- statement:
--   Let $r, d \in \mathbb N$ and $m \ge 1$. Let $\tilde f = \sum_a c(a) X^a$ be a polynomial in $m$ variables with degree at most $d-1$ in each variable and coefficients $c(a) \in \{0,\dots,r-1\}$, and let $\tilde\alpha \in \{0,\dots,r-1\}^m$. Then the value $V = \tilde f(\tilde\alpha) = \sum_a c(a) \prod_j \tilde\alpha_j^{a_j}$ satisfies
--   $$V \le d^m (r-1)^{md} \qquad\text{and}\qquad V < \prod_{\substack{p \text{ prime} \\ p \le \ell}} p, \qquad \ell = \bigl\lfloor 16 \ln \max(2,\ d^m(r-1)^{md}) \bigr\rfloor .$$
--
--   So the integer $\tilde f(\tilde\alpha_i)$ is determined by its residues modulo the primes $p_1,\dots,p_k \le \ell$ computed in Step 2 of Algorithm MULTIMODULAR, which is the correctness half of Theorem 4.2.
--
--   **Formalization Note** $\ell$ is `ellValue d m r`, the number the algorithm uses. Nonnegativity of $V$ is automatic in $\mathbb N$.
--
--   Differences from the source:
--   - correction: ℓ = 16 log(d^m (r−1)^{md}) → ℓ = ⌊16 ln max(2, d^m (r−1)^{md})⌋; reason: counterexample: r = 2, m = d = 1, f̃ = 1, α̃ = 0: d^m(r−1)^{md} = 1, the printed ℓ is 0, the product of the primes ≤ 0 is 1, and f̃(α̃) = 1 is not < 1; for d^m(r−1)^{md} ≥ 2 the two ℓ agree
--   - correction: all m (including m = 0) → 1 ≤ m; reason: counterexample: m = 0, r = 3, d = 1, f̃ = 2: f̃(α̃) = 2 > 1 = d^0 (r−1)^0; the bound needs m(d−1)+1 ≤ md
--   - reading: log in ℓ (base not stated) → natural logarithm; reason: the reading of Lemma 2.4 used throughout (the stronger one)
--   - encoding: f̃ ∈ ℤ[X], α̃_i ∈ ℤ^m with entries in {0, …, r−1}; 0 ≤ f̃(α̃_i); p_1 ⋯ p_k → ℕ-valued table and point with entries < r; value in ℕ; primorial ℓ; reason: the lifts are nonnegative; same instances
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), proof of Theorem 4.2, p. 13 (first sentence)

import Mathlib
import Definitions.Def_KUMultimodular_multimodular

namespace KUMultimodular

/-- **The correctness bound in the proof of Theorem 4.2** (Kedlaya–Umans, Dagstuhl Seminar
Proceedings 08381 (2008), p. 13): `0 ≤ f̃(α̃_i) ≤ d^m (r-1)^{md} < p_1 ⋯ p_k`. Let `m ≥ 1`, let
`c` be a coefficient table with entries in `{0, …, r-1}` (the lift `f̃`, degree at most `d - 1` in
each variable) and `a` a point with coordinates in `{0, …, r-1}` (the lift `α̃_i`). Then the value
`V = f̃(a)` satisfies `V ≤ d^m (r-1)^{md}` and `V` is smaller than the product of the primes
`≤ ℓ`, for the algorithm's `ℓ = ⌊16 log (max 2 (d^m (r-1)^{md}))⌋` (`ellValue`). -/
theorem lifted_value_lt_primorial (r m d : ℕ) (hm : 1 ≤ m) (c : (Fin m → Fin d) → ℕ)
    (hc : ∀ k, c k < r) (a : Fin m → ℕ) (ha : ∀ j, a j < r) :
    (∑ k, c k * ∏ j, a j ^ (k j : ℕ)) ≤ d ^ m * (r - 1) ^ (m * d) ∧
      (∑ k, c k * ∏ j, a j ^ (k j : ℕ)) < primorial (ellValue d m r) := by sorry

end KUMultimodular
