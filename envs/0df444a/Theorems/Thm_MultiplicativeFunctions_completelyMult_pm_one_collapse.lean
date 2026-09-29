-- Prove2me | Theorems.Thm_MultiplicativeFunctions_completelyMult_pm_one_collapse
-- name    : MultiplicativeFunctions.completelyMult_pm_one_collapse
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:12:03.364539+00:00
-- url     : https://prove2.me/theorems/76e57e81-7d25-42d9-82dc-83f7955f1589
-- title:
--   Completely multiplicative $\pm1$ functions satisfy the shift relation
-- statement:
--   **Complete multiplicativity forces invariance of the two-point correlation under prime
--   dilation.**
--
--   Let $f : \mathbb{N} \to \mathbb{R}$ be completely multiplicative, $f(ab) = f(a)f(b)$ for all
--   $a,b$, and suppose $f(p) = \pm1$ at every prime $p$. Then for every prime $p$ and every $N$,
--
--   $$f(pN)\,f(pN+p) \;=\; f(N)\,f(N+1).$$
--
--   The computation is immediate once both sides are factored: $f(pN) = f(p)f(N)$ and, since
--   $pN + p = p(N+1)$, also $f(pN+p) = f(p)f(N+1)$. Multiplying,
--
--   $$f(pN)f(pN+p) = f(p)^{2}f(N)f(N+1) = f(N)f(N+1),$$
--
--   because $f(p)^{2} = 1$ for a $\pm1$-valued $f$. The hypothesis that $f$ takes only the values
--   $\pm1$ **at primes** is exactly what is needed — the square of the prime value must be $1$,
--   and no constraint on $f$ elsewhere is used.
--
--   This is the easy direction of the characterisation of $\pm1$-valued completely multiplicative
--   functions by their two-point correlations, the converse being the substantial statement. The
--   relation says the correlation $f(n)f(n+1)$ is unchanged by dilating $n$ by a prime, which is
--   the invariance exploited in the Chowla and Erd\H{o}s-discrepancy circle of problems.
--
--   **Formalization note.** `hCM` is complete multiplicativity (no coprimality hypothesis), and
--   `hpm` constrains $f$ only at primes.
-- source:
--   Arising in the Chowla / Erdős-discrepancy circle; cf. Elliott, *Probabilistic Number Theory*. Lean proof extracted from `Salt/Entropy/Chowla/BoundaryMap.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace MultiplicativeFunctions

theorem completelyMult_pm_one_collapse (f : ℕ → ℝ)
    (hCM : ∀ a b, f (a * b) = f a * f b)
    (hpm : ∀ p, p.Prime → f p = 1 ∨ f p = -1) :
    ∀ p N, p.Prime → f (p * N) * f (p * N + p) = f N * f (N + 1) := by sorry

end MultiplicativeFunctions
