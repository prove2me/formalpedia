-- Prove2me | Theorems.Thm_LuoSunLiu_DIP_lemma_S6
-- name    : LuoSunLiu.DIP.lemma_S6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:14:05.385418+00:00
-- url     : https://prove2.me/theorems/73982d7c-6dc0-4647-841f-770e44b8a2bd
-- title:
--   Lemma S6, p. 49 — √(β*_{T₀} log((dλ + T₀p²_max)/(dλ))) ≤ C′₁√d log(C′₂T₀)
-- statement:
--   Let $p_{\max} > 0$, $\lambda > 0$ and $C_1 \ge 0$. For $d \ge 1$ and $T_0 \ge 1$ write
--   $$\beta^*_{T_0} = p_{\max}^2\Bigl(1 \vee \Bigl(C_1\sqrt{\lambda d} + \sqrt{2\log T_0 + d\log\tfrac{d\lambda + (T_0-1)p_{\max}^2}{d\lambda}}\Bigr)^2\Bigr).$$
--   There exist constants $C'_1, C'_2 > 0$, depending only on $p_{\max}$, $\lambda$ and $C_1$, such that for every $d \ge 1$ and every $T_0 \ge 1$,
--   $$\sqrt{\beta^*_{T_0}\log\frac{d\lambda + T_0p_{\max}^2}{d\lambda}} \le C'_1\sqrt d\,\log(C'_2T_0).$$
--
--   This converts the confidence term of Proposition 4, with $\delta = 1/T_0$, into the $\sqrt d\log T_0$ form used for the expected bound of Proposition 3.
--
--   **Formalization Note** The paper fixes $d$ in the context and quantifies the constants before $T_0$. The constants of its proof, $C'_1 = \max\{p_{\max}, p_{\max}C_1\sqrt\lambda + \sqrt3p_{\max}\}$ and $C'_2 = \max\{1 + p_{\max}^2/\lambda, 3\}$, do not depend on $d$, and Proposition 3 needs this because $d$ grows with $T_0$; so the constants are placed before $d$.
-- source:
--   Luo, Sun and Liu, arXiv:2109.07340v2, p. 49, Lemma S6; proof pp. 49–51

import Mathlib

namespace LuoSunLiu.DIP

/-- Lemma S6 (Luo, Sun and Liu, arXiv:2109.07340v2, p. 49; proof pp. 49–51). For
`β*_{T₀} = p²_max(1 ∨ (C₁√(λd) + √(2 log T₀ + d log((dλ + (T₀-1)p²_max)/(dλ))))²)` there are
constants `C′₁, C′₂ > 0`, not depending on `d` or `T₀`, such that for every `d ≥ 1` and `T₀ ≥ 1`,
`√(β*_{T₀} log((dλ + T₀p²_max)/(dλ))) ≤ C′₁ √d log(C′₂T₀)`. -/
theorem lemma_S6 (pmax lam C1 : ℝ) (hpmax : 0 < pmax) (hlam : 0 < lam) (hC1 : 0 ≤ C1) :
    ∃ C1' C2' : ℝ, 0 < C1' ∧ 0 < C2' ∧ ∀ d : ℕ, 1 ≤ d → ∀ T0 : ℕ, 1 ≤ T0 →
      Real.sqrt (pmax ^ 2 * max 1 ((C1 * Real.sqrt (lam * d) +
          Real.sqrt (2 * Real.log T0 +
            d * Real.log ((d * lam + ((T0 : ℝ) - 1) * pmax ^ 2) / (d * lam)))) ^ 2) *
        Real.log ((d * lam + T0 * pmax ^ 2) / (d * lam))) ≤
        C1' * Real.sqrt d * Real.log (C2' * T0) := by sorry

end LuoSunLiu.DIP
