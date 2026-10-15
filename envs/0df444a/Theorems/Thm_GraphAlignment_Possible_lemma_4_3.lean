-- Prove2me | Theorems.Thm_GraphAlignment_Possible_lemma_4_3
-- name    : GraphAlignment.Possible.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:27.773446+00:00
-- url     : https://prove2.me/theorems/0769e88f-fb6c-4990-b4d5-4dc5c78775b9
-- title:
--   Lemma 4.3, p. 16 — min over z of z^{−τ} e^{q₂(z²−1)+q₁(z−1)} is at most ζ^τ, and the minimizer satisfies (13)
-- statement:
--   Let $\tau > 0$, $q_1 \ge 0$ and $q_2 > 0$, and let
--   $$f(z) = z^{-\tau}\, e^{q_2(z^2-1) + q_1(z-1)}, \qquad z > 0,$$
--   $$\zeta = \max\Big\{\frac{\sqrt2\, e\, q_1}{\tau},\ 4e\Big(\frac{q_2}{\tau}\Big)^{1/2}\Big\}.$$
--   Then $f$ attains its minimum on $(0,\infty)$, and every minimizer $z^*$ satisfies
--   $$f(z^*) \le \zeta^\tau \quad (12), \qquad z^{*2} = \frac{\tau - q_1 z^*}{2q_2} \le \frac{\tau}{2q_2} \quad (13).$$
--
--   This optimises the Chernoff bound for the overlap of a bad permutation in Proposition 4.4.
--
--   **Formalization Note** The paper states $\tau \ge 0$, $q_1 \ge 0$, $q_2 \ge 0$ and minimises over $z \ge 0$. Here $\tau > 0$ and $q_2 > 0$, because $\zeta$ divides by $\tau$ and (13) by $q_2$ (with $q_1 = q_2 = 0$ there is no minimizer). The variable ranges over $z > 0$: at $z = 0$ the paper's $z^{-\tau}$ is $+\infty$, while Lean's real power gives $0^{-\tau} = 0$, which would make (12) trivial. The existence of a minimizer is part of the statement. $z^{-\tau}$ and $\zeta^\tau$ are real powers.
-- source:
--   Hall, Massoulié, Partial Recovery in the Graph Alignment Problem, arXiv:2007.00533v5, p. 16, Lemma 4.3, (12)–(13)

import Mathlib

namespace GraphAlignment.Possible

theorem lemma_4_3 (τ q1 q2 : ℝ) (hτ : 0 < τ) (hq1 : 0 ≤ q1) (hq2 : 0 < q2) :
    let f : ℝ → ℝ := fun z => z ^ (-τ) * Real.exp (q2 * (z ^ 2 - 1) + q1 * (z - 1))
    let ζ : ℝ := max (Real.sqrt 2 * Real.exp 1 * q1 / τ) (4 * Real.exp 1 * Real.sqrt (q2 / τ))
    (∃ z, 0 < z ∧ IsMinOn f (Set.Ioi 0) z) ∧
      ∀ z, 0 < z → IsMinOn f (Set.Ioi 0) z →
        f z ≤ ζ ^ τ ∧ z ^ 2 = (τ - q1 * z) / (2 * q2) ∧
          (τ - q1 * z) / (2 * q2) ≤ τ / (2 * q2) := by sorry

end GraphAlignment.Possible
