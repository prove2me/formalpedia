-- Prove2me | Theorems.Thm_JSQHalfinWhitt_Tightness_eq_3_18
-- name    : JSQHalfinWhitt.Tightness.eq_3_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:57.466453+00:00
-- url     : https://prove2.me/theorems/53920918-95a5-4ea9-a92c-8632b4d2e0c6
-- title:
--   Section 3, (3.18) — $\mathbb E((X_2 - \kappa/\sqrt n)\vee 0) \le \frac{1}{\beta\sqrt n}(12 + \frac{6\kappa}{\kappa-\beta})\mathbb P(X_2 \ge \kappa/\sqrt n - 1/n)$
-- statement:
--   Let $n \ge 1$ and $0 < \beta < \sqrt n$, fix $\kappa > \beta$, and let $Q$ have a stationary distribution of the join-the-shortest-queue chain with $n$ servers and $\lambda = 1 - \beta/\sqrt n$. With $X_2 = Q_2/n$,
--   $$\mathbb E\big((X_2 - \kappa/\sqrt n)\vee 0\big) \le \frac{1}{\beta\sqrt n}\Big(12 + \frac{6\kappa}{\kappa - \beta}\Big)\,\mathbb P\big(X_2 \ge \kappa/\sqrt n - 1/n\big). \tag{3.18}$$
--
--   This inequality is the core estimate of the paper's Section 3. Multiplying by $\sqrt n$ bounds $\mathbb E\sqrt n X_2$ by a constant depending only on $\beta$, which gives (2.2) for $i = 2$; a bootstrapping argument based on (3.18) gives (2.3).
--
--   **Formalization Note** Expectations and probabilities are sums against the stationary distribution $\pi$ (global balance $\pi G_Q = 0$); all summands are bounded. Lean's `q.1 1` is $Q_2$. The display is unnumbered as a lemma; it is cited by its equation number.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), p. 10, Section 3, (3.18) (setting fixed on p. 9: 'Fix κ > β and let f^*(x) be as in Lemma 4')

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Stationary
import Definitions.Def_JSQHalfinWhitt_Tightness_Model

namespace JSQHalfinWhitt.Tightness

/-- (3.18) (Braverman, p. 10): for `κ > β` and every stationary distribution `π` of the JSQ chain
with `λ = 1 − β/√n`, with `X_2 = Q_2/n` (Lean `q.1 1 / n`),
`E((X_2 − κ/√n) ∨ 0) ≤ (1/(β√n))(12 + 6κ/(κ − β)) P(X_2 ≥ κ/√n − 1/n)`. -/
theorem eq_3_18 (n : ℕ) (β κ : ℝ) (hn : 1 ≤ n) (hβ : 0 < β) (hβn : β < Real.sqrt n)
    (hκ : β < κ) (π : State n → ℝ) (hπ : IsStationaryDist (genQ n (lamHW β n)) π) :
    expect π (fun q => max ((q.1 1 : ℝ) / n - κ / Real.sqrt n) 0) ≤
      1 / (β * Real.sqrt n) * (12 + 6 * κ / (κ - β)) *
        prob π (fun q => κ / Real.sqrt n - 1 / n ≤ (q.1 1 : ℝ) / n) := by sorry

end JSQHalfinWhitt.Tightness
