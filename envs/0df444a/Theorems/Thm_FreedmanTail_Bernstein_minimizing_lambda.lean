-- Prove2me | Theorems.Thm_FreedmanTail_Bernstein_minimizing_lambda
-- name    : FreedmanTail.Bernstein.minimizing_lambda
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:09:07.802726+00:00
-- url     : https://prove2.me/theorems/784ef699-ff4e-4490-a9c2-f39a063bbb20
-- title:
--   Proof of (4.1) — λ₀ = log[(a+b)/b] minimizes exp[−λa + e(λ)b] over λ ≥ 0, with value (b/(a+b))^{a+b} e^a
-- statement:
--   Let $a>0$, $b>0$ and $e(\lambda)=e^\lambda-1-\lambda$, and put $\lambda_0=\log[(a+b)/b]$. Then $\lambda_0\ge0$, $\lambda_0$ minimizes $\lambda\mapsto\exp[-\lambda a+e(\lambda)b]$ over $\lambda\ge0$, and the minimum value is the first bound of Theorem (4.1):
--   $$\exp[-\lambda_0a+e(\lambda_0)b]=\Bigl(\frac{b}{a+b}\Bigr)^{a+b}e^{a}\le\exp[-\lambda a+e(\lambda)b]\qquad\text{for all }\lambda\ge0 .$$
--
--   Combined with the bound $P\{A\}\le\exp[-\lambda a+e(\lambda)b]$, valid for every $\lambda\ge0$, this yields the Bennett-type bound of (4.1).
--
--   **Formalization Note** $(b/(a+b))^{a+b}$ is a real power of a number in $(0,1)$, and $\log$ is the natural logarithm.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 108 (PDF p. 9), proof of (4.1) Theorem, second sentence

import Mathlib
import Definitions.Def_FreedmanTail_Bernstein_Exponents

namespace FreedmanTail.Bernstein

/-- Freedman (1975), proof of (4.1) Theorem, p. 108: for positive `a, b`, the λ ≥ 0 minimizing
`exp[−λa + e(λ)b]` is `λ₀ = log[(a + b)/b]`, and the minimum is `(b/(a+b))^{a+b} e^a`. -/
theorem minimizing_lambda (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 ≤ Real.log ((a + b) / b) ∧
      (∀ lam : ℝ, 0 ≤ lam →
        Real.exp (-Real.log ((a + b) / b) * a + e (Real.log ((a + b) / b)) * b)
          ≤ Real.exp (-lam * a + e lam * b)) ∧
      Real.exp (-Real.log ((a + b) / b) * a + e (Real.log ((a + b) / b)) * b)
        = (b / (a + b)) ^ (a + b) * Real.exp a := by sorry

end FreedmanTail.Bernstein
