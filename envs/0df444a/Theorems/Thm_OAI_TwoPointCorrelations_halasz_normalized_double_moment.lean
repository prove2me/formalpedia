-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_normalized_double_moment
-- name    : OAI.TwoPointCorrelations.halasz_normalized_double_moment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:12.343166+00:00
-- url     : https://prove2.me/theorems/3a491279-a32e-4e25-a223-6d39aac8d9e6
-- title:
--   From a Vinogradov mean-value bound to a moment bound for the scaled Weyl sum
-- statement:
--   Let $k,r,M$ be naturals with $r,M\ge1$, $\gamma\in\mathbb R^k$ with every $\gamma_j\ne0$, and reals $C,\varepsilon$ such that $J_{r,k}(M)\le C\,M^{2r-k(k+1)/2+\varepsilon}$, where $J_{r,k}(M)$ is the Vinogradov count `halaszVinogradovCount r k M`. Then
--
--   $$\Big|\sum_{b=1}^MV_{k,M}\big((\gamma_jb^j)_{j=1}^k\big)\Big|^{2r^2}\le(32r)^k\,C^2\,M^{4r^2+2\varepsilon}\prod_{j=1}^k w_j,$$
--
--   where $V_{k,M}(\alpha)=\sum_{n=1}^Me(\sum_jn^j\alpha_j)$ (`halaszVinogradovPolynomial`), the products $\gamma_jb^j$ are taken modulo $1$, and $w_j$ = `halaszNormalizedWeight r M γ j` $=\min\big(2r+1,\ \tfrac52M^{-j}+2r|\gamma_j|+\tfrac1{2rM^{2j}|\gamma_j|}\big)$ (with $j$ counted from $1$).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_normalized_double_moment`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset

theorem halasz_normalized_double_moment {k r M : ℕ} (hr : 1≤ r) (hM : 1≤ M)
    (γ : Fin k → ℝ) (hγ : ∀ j,γ j≠0) {C ε : ℝ}
    (hJ : (halaszVinogradovCount r k M:ℝ)≤
      C*(M:ℝ)^(2*(r:ℝ)-((∑ j : Fin k,(j.val+1):ℕ):ℝ)+ε)) :
    ‖∑ b : Fin M,halaszVinogradovPolynomial k M
      (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^(2*r*r) ≤
      (32*(r:ℝ))^k*C^2*(M:ℝ)^(4*(r:ℝ)^2+2*ε)*
        ∏ j,halaszNormalizedWeight r M γ j := by
  sorry

end OAI.TwoPointCorrelations
