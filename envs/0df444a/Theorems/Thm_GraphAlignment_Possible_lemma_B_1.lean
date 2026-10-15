-- Prove2me | Theorems.Thm_GraphAlignment_Possible_lemma_B_1
-- name    : GraphAlignment.Possible.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:19.297185+00:00
-- url     : https://prove2.me/theorems/769aa383-df79-4ccb-a6d8-ed0c1cc2e572
-- title:
--   Lemma B.1, p. 23 — (αᵏ + βᵏ)^{n/k} ≤ (α² + β²)^{n/2} for 2 ≤ k ≤ n
-- statement:
--   Let $n \in \mathbb N$ and $2 \le k \le n$, and let $\alpha, \beta$ be positive real numbers. Then
--   $$(\alpha^k + \beta^k)^{n/k} \le (\alpha^2 + \beta^2)^{n/2}.$$
--
--   It is the monotonicity of $\ell^p$ norms of a two-entry vector, used to compare the contributions of long cycles with that of a cycle of length 2 in the proof of Proposition 4.4.
--
--   **Formalization Note** The exponents $n/k$ and $n/2$ are real numbers (`Real.rpow`).
-- source:
--   Hall, Massoulié, Partial Recovery in the Graph Alignment Problem, arXiv:2007.00533v5, p. 23, Lemma B.1

import Mathlib

namespace GraphAlignment.Possible

theorem lemma_B_1 (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (α ^ k + β ^ k) ^ ((n : ℝ) / k) ≤ (α ^ 2 + β ^ 2) ^ ((n : ℝ) / 2) := by sorry

end GraphAlignment.Possible
