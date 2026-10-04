-- Prove2me | Theorems.Thm_OnlineRandomization_Tightness_params_solve
-- name    : OnlineRandomization.Tightness.params_solve
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:33:22.603708+00:00
-- url     : https://prove2.me/theorems/63e0b671-3217-4fee-9172-909752192e45
-- title:
--   §2, p. 12 — $m(t)$ and $M(t)$ are the unique solution of the two equations defining the mates game
-- statement:
--   Let $\alpha, \beta > 0$ and let $t \ge 2$ be an integer. Put
--   $$
--   m(t) = \frac{1 + (2t-1)(2t\beta - 1) - 2\alpha}{(2t-2)(\alpha + 2t - 1)}, \qquad M(t) = \frac{2t\alpha\beta + \alpha - 1}{\alpha + 2t - 1}.
--   $$
--   Then $2 + (2t-2)m(t) > 0$, the pair $(m, M) = (m(t), M(t))$ satisfies the simultaneous equations
--   $$
--   \beta = \frac{(2t-2)m + M + 1}{2t}, \qquad \alpha = \frac{1 + (2t-1)M}{2 + (2t-2)m},
--   $$
--   and it is the only pair of reals that satisfies them.
--
--   This makes precise the paper's statement that $m$ and $M$ are "determined by" the two equations: the first equation is $G$'s expected cost against an oblivious adversary, the second is $G$'s competitive ratio against an adaptive on-line adversary.
--
--   **Formalization Note.** The terms $2t-1$, $2t-2$ are computed in $\mathbb R$, so there is no natural-number subtraction. For the uniqueness clause no nonvanishing hypothesis is needed on the second denominator: a zero denominator would make Lean's quotient $0$, contradicting $\alpha > 0$.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 12, §2, first paragraph (the simultaneous equations for m and M)

import Mathlib
import Definitions.Def_OnlineRandomization_Tightness_Model
import Definitions.Def_OnlineRandomization_Tightness_MatesGame

namespace OnlineRandomization.Tightness

/-- Manuscript p. 12, first paragraph: for positive `α, β` and every integer `t ≥ 2`, the
closed forms `m(t)`, `M(t)` are the unique solution of the simultaneous equations
`β = ((2t − 2)m + M + 1)/(2t)` and `α = (1 + (2t − 1)M)/(2 + (2t − 2)m)`, and the second
denominator is positive. -/
theorem params_solve (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (t : ℕ) (ht : 2 ≤ t) :
    β = ((2 * (t : ℝ) - 2) * paramSmall α β t + paramLarge α β t + 1) / (2 * (t : ℝ)) ∧
    α = (1 + (2 * (t : ℝ) - 1) * paramLarge α β t) /
      (2 + (2 * (t : ℝ) - 2) * paramSmall α β t) ∧
    0 < 2 + (2 * (t : ℝ) - 2) * paramSmall α β t ∧
    ∀ m M : ℝ, β = ((2 * (t : ℝ) - 2) * m + M + 1) / (2 * (t : ℝ)) →
      α = (1 + (2 * (t : ℝ) - 1) * M) / (2 + (2 * (t : ℝ) - 2) * m) →
      m = paramSmall α β t ∧ M = paramLarge α β t := by sorry

end OnlineRandomization.Tightness
