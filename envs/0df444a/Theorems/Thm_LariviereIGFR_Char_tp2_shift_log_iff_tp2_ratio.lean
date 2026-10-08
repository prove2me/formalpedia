-- Prove2me | Theorems.Thm_LariviereIGFR_Char_tp2_shift_log_iff_tp2_ratio
-- name    : LariviereIGFR.Char.tp2_shift_log_iff_tp2_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:38:04.389984+00:00
-- url     : https://prove2.me/theorems/c3af3b09-019a-4b5f-b071-bb7cdee4c58e
-- title:
--   Proof of Theorem 1, p. 603 — Φ̄_L(ξ − θ) TP₂ on ℝ² iff Φ̄(ξ/θ) TP₂ on (0, ∞)²
-- statement:
--   Let $X \ge 0$ have law $\mu$ with distribution function $\Phi$ and regular density $\varphi$, and let $\bar\Phi_L$ be the survival function of $X_L = \log X$. Then
--   $$f_L(\xi, \theta) = \bar\Phi_L(\xi - \theta) \text{ is TP}_2 \text{ on } \mathbb R \times \mathbb R \iff f(\xi, \theta) = \bar\Phi(\xi/\theta) \text{ is TP}_2 \text{ on } (0,\infty) \times (0,\infty).$$
--
--   This is the last step of the proof of Theorem 1 ("which is equivalent to part 4"): after Barlow–Proschan it connects part 2 with part 4.
--
--   **Formalization Note** The paper gives no domain for $\bar\Phi(\xi/\theta)$. $\theta > 0$ is forced by the division (Lean's $\xi/0 = 0$ would otherwise enter), and $\xi > 0$ loses nothing: for $\xi \le 0$ and $\theta > 0$, $\bar\Phi(\xi/\theta) = 1$ because $X \ge 0$ has no atom at $0$.
-- source:
--   Lariviere, A note on probability distributions with increasing generalized failure rates, Oper. Res. 54(3) (2006), p. 603, §2, proof of Theorem 1 ("which is equivalent to part 4")

import Mathlib
import Definitions.Def_LariviereIGFR_Char_Setting

namespace LariviereIGFR.Char

open MeasureTheory ProbabilityTheory

theorem tp2_shift_log_iff_tp2_ratio (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hnn : μ (Set.Iio 0) = 0) (hφ : IsRegDensity μ φ) :
    IsTP2On (fun ξ θ => survival (μ.map Real.log) (ξ - θ)) Set.univ Set.univ ↔
      IsTP2On (fun ξ θ => survival μ (ξ / θ)) (Set.Ioi 0) (Set.Ioi 0) := by sorry

end LariviereIGFR.Char
