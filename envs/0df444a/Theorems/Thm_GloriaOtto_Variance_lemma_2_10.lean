-- Prove2me | Theorems.Thm_GloriaOtto_Variance_lemma_2_10
-- name    : GloriaOtto.Variance.lemma_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:15.984784+00:00
-- url     : https://prove2.me/theorems/816ee2fa-ea77-4f63-98f6-adfbd2564979
-- title:
--   Lemma 2.10 — dyadic-annulus L² bounds on h_T imply Σ_{|x|≤R} Σ_z h_T(z)h_T(z−x) ≲ R² max{1, ln(√T/R)} (d = 2), ≲ R² (d > 2)
-- statement:
--   Let $d \ge 2$. For all constants $C_1$ and $R_0 > 0$ there are constants $C_2$ and $R_1$ (depending only on $d, C_1, R_0$) with the following property. Let $T > 0$ and $h_T : \mathbb Z^d \to \mathbb R$ satisfy, for every $R \ge R_0$,
--   $$\sum_{R<|z|\le 2R} h_T(z)^2 \le C_1\min\{1,\sqrt T R^{-1}\}^2 \ \ (d=2), \qquad \sum_{R<|z|\le 2R} h_T(z)^2 \le C_1 R^{2-d}\ \ (d>2), \tag{2.26–2.27}$$
--   and
--   $$\sum_{|z|\le R_0} h_T(z)^2 \le C_1. \tag{2.28}$$
--   Then for every $R \ge R_1$,
--   $$\sum_{|x|\le R}\sum_{z\in\mathbb Z^d}|h_T(z)|\,|h_T(z-x)| \le C_2 R^2\max\{1,\ln(\sqrt T R^{-1})\}\ \ (d=2), \qquad \le C_2 R^2 \ \ (d > 2). \tag{2.29–2.30}$$
--
--   This is a deterministic convolution estimate: square-averaged decay on dyadic annuli implies optimal decay of the convolution of $|h_T|$ with itself, in a linear average.
--
--   **Formalization Note.** "$R \gg 1$" in the hypotheses is $R \ge R_0$, and "$R\sim1$" in (2.28) is pinned to the same radius $R_0$; "$R\gg1$" in the conclusion is $R \ge R_1$. The left side of the conclusion is summed in $[0,\infty]$ with $|h_T|$, which is at least the paper's signed sum and makes its finiteness part of the conclusion.
-- source:
--   Gloria, Otto, arXiv:1104.1291v1, Lemma 2.10, (2.26)–(2.30), p. 20

import Mathlib
import Definitions.Def_GloriaOtto_Variance_Setup

open MeasureTheory ProbabilityTheory

namespace GloriaOtto.Variance

theorem lemma_2_10 (d : ℕ) (hd : 2 ≤ d) :
    ∀ C₁ R₀ : ℝ, 0 < R₀ → ∃ C₂ R₁ : ℝ, ∀ T : ℝ, 0 < T → ∀ h : Site d → ℝ,
      (∀ R : ℝ, R₀ ≤ R →
        ∑' z, {z : Site d | R < latNorm z ∧ latNorm z ≤ 2 * R}.indicator (fun z => h z ^ 2) z
          ≤ C₁ * (if d = 2 then (min 1 (Real.sqrt T / R)) ^ 2 else R ^ (2 - (d : ℝ)))) →
      ∑' z, {z : Site d | latNorm z ≤ R₀}.indicator (fun z => h z ^ 2) z ≤ C₁ →
      ∀ R : ℝ, R₁ ≤ R →
        ∑' x, {x : Site d | latNorm x ≤ R}.indicator
            (fun x => ∑' z, ‖h z‖ₑ * ‖h (z - x)‖ₑ) x
          ≤ ENNReal.ofReal (C₂ * (if d = 2 then R ^ 2 * max 1 (Real.log (Real.sqrt T / R))
              else R ^ 2)) := by sorry

end GloriaOtto.Variance
