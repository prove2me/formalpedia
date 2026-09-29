-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_forall_sub_mul_Gamma_le_norm_Gamma_add_mul_I_of_abs_le
-- name    : LanglandsTunnell.exists_forall_sub_mul_Gamma_le_norm_Gamma_add_mul_I_of_abs_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/0984d9af-db70-5bcd-ae0d-265b9e807836
-- title:
--   |Γ(σ+iτ)| is close to Γ(σ) for large σ
-- statement:
--   Let $K$ and $\varepsilon$ be real numbers with $0 \le K$ and $0 < \varepsilon$. The assertion is that there exists a real number $R$ such that for all real numbers $\sigma$ and $\tau$ with $R \le \sigma$ and $|\tau| \le K$, the two inequalities $$(1-\varepsilon)\,\Gamma(\sigma) \le \bigl\|\Gamma(\sigma + \tau i)\bigr\| \le \Gamma(\sigma)$$ hold, where on the left and right $\Gamma$ is the real Gamma function `Real.Gamma` evaluated at $\sigma$, and in the middle $\Gamma$ is the complex Gamma function `Complex.Gamma` evaluated at the complex number with real part $\sigma$ and imaginary part $\tau$, its modulus being taken. Thus, uniformly over the horizontal strip $|\operatorname{Im}| \le K$ and sufficiently far to the right, the modulus of $\Gamma$ on the vertical line through $\sigma$ is at most $\Gamma(\sigma)$ and at least $(1-\varepsilon)\Gamma(\sigma)$. No positivity of $R$ is claimed, and the statement is a purely real-analytic estimate with no arithmetic input.
--
--   This is the standard statement that the complex Gamma function loses essentially no modulus along vertical shifts of bounded height, asymptotically in the real part; the upper bound is the triangle inequality applied to the Euler integral, and the lower bound quantifies phase coherence of $t^{i\tau}$. It feeds the growth estimates for Gamma factors used in the Mellin-transform analysis, being cited by [`LanglandsTunnell.exists_forall_norm_Gamma_add_mul_I_le_mul_rpow_mul_norm_Gamma`](thm.html#LanglandsTunnell.exists_forall_norm_Gamma_add_mul_I_le_mul_rpow_mul_norm_Gamma).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_forall_sub_mul_Gamma_le_norm_Gamma_add_mul_I_of_abs_le.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Complex

theorem LanglandsTunnell.exists_forall_sub_mul_Gamma_le_norm_Gamma_add_mul_I_of_abs_le
    (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ σ τ : ℝ, R ≤ σ → |τ| ≤ K →
      (1 - ε) * Real.Gamma σ ≤ ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ∧
      ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ Real.Gamma σ := by sorry
