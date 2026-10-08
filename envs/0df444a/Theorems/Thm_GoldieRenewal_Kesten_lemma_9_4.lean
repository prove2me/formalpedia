-- Prove2me | Theorems.Thm_GoldieRenewal_Kesten_lemma_9_4
-- name    : GoldieRenewal.Kesten.lemma_9_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:09:14.078628+00:00
-- url     : https://prove2.me/theorems/4dc48cf3-f6d1-44db-9b8c-bb0e66107369
-- title:
--   Lemma 9.4 — ∫₀^∞ |P(X > t) − P(Y > t)| t^{κ−1} dt ≤ κ⁻¹E|(X⁺)^κ − (Y⁺)^κ|, and (9.18) when finite
-- statement:
--   Let $\kappa>0$ and let $X$, $Y$ be real random variables on a common probability space; $x^+ = x\vee 0$.
--
--   1. (9.17), as an inequality in $[0,\infty]$:
--   $$
--   \int_0^\infty \big|P(X>t)-P(Y>t)\big|\,t^{\kappa-1}\,dt \;\le\; \frac1\kappa\,\mathbf E\big|(X^+)^\kappa-(Y^+)^\kappa\big| .
--   $$
--   2. (9.18): if $\mathbf E\big|(X^+)^\kappa-(Y^+)^\kappa\big|<\infty$, then $t\mapsto (P(X>t)-P(Y>t))t^{\kappa-1}$ is integrable on $(0,\infty)$ and
--   $$
--   \int_0^\infty \big(P(X>t)-P(Y>t)\big)\,t^{\kappa-1}\,dt = \frac1\kappa\,\mathbf E\big((X^+)^\kappa-(Y^+)^\kappa\big).
--   $$
--
--   The lemma converts the tail-difference integrals of the implicit renewal theorem into moment expressions; it is what turns Theorem 2.3 into Corollary 2.4.
--
--   **Formalization Note** The paper prints (9.17) as an equality "finite or infinite". Equality fails in general (for $X$, $Y$ independent and identically distributed and non-degenerate the left side is $0$ while the right side is positive); the paper's proof establishes, and Corollary 2.4 uses, only the inequality, which is what is stated. Both sides of (9.17) are lower Lebesgue integrals, so infinite values are allowed.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 149, Lemma 9.4, (9.17)–(9.18)

import Mathlib

namespace GoldieRenewal.Kesten

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Lemma 9.4** (Goldie, *Implicit renewal theory and tails of solutions of random equations*,
Ann. Appl. Probab. 1(1) (1991), p. 149). Let `κ > 0` and let `X`, `Y` be random variables on a
common probability space.

* (9.17), corrected to an inequality:
  `∫₀^∞ |P(X > t) − P(Y > t)| t^{κ−1} dt ≤ κ⁻¹ E|(X⁺)^κ − (Y⁺)^κ|`, finite or infinite.
* (9.18): when `E|(X⁺)^κ − (Y⁺)^κ| < ∞`, the function `t ↦ (P(X > t) − P(Y > t)) t^{κ−1}` is
  integrable on `(0, ∞)` and `∫₀^∞ (P(X > t) − P(Y > t)) t^{κ−1} dt = κ⁻¹ E((X⁺)^κ − (Y⁺)^κ)`.

**Formalization Note** (9.17) is printed as an equality; only `≤` holds (for `X`, `Y` i.i.d. and
non-degenerate the left side is `0` and the right side positive), and the paper's proof and its
use in Corollary 2.4 need only `≤`. Both sides of (9.17) are lower Lebesgue integrals in `[0, ∞]`,
so "finite or infinite" is literal. `x⁺ = max x 0`. -/
theorem lemma_9_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) :
    (∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (|P.real {ω | t < X ω} - P.real {ω | t < Y ω}| * t ^ (κ - 1))
      ≤ ENNReal.ofReal κ⁻¹ *
        ∫⁻ ω, ENNReal.ofReal |(max (X ω) 0) ^ κ - (max (Y ω) 0) ^ κ| ∂P) ∧
    (Integrable (fun ω => (max (X ω) 0) ^ κ - (max (Y ω) 0) ^ κ) P →
      IntegrableOn (fun t : ℝ => (P.real {ω | t < X ω} - P.real {ω | t < Y ω}) * t ^ (κ - 1))
          (Set.Ioi 0) ∧
        ∫ t in Set.Ioi (0 : ℝ), (P.real {ω | t < X ω} - P.real {ω | t < Y ω}) * t ^ (κ - 1)
          = κ⁻¹ * ∫ ω, ((max (X ω) 0) ^ κ - (max (Y ω) 0) ^ κ) ∂P) := by sorry

end GoldieRenewal.Kesten
