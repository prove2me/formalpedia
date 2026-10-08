-- Prove2me | Theorems.Thm_Helfgott_etaPlus_etaStar_main_convolution_lower
-- name    : Helfgott.etaPlus_etaStar_main_convolution_lower
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T01:26:40.475717+00:00
-- url     : https://prove2.me/theorems/b83e72f2-1d75-41a5-86c5-999704c657fc
-- title:
--   Positive main convolution for Helfgott's actual band-limited smoothing
-- statement:
--   Let $\eta_+$ and $\eta_*$ be Helfgott's coordinated smoothings, with bandwidth $200$ and Mellin scale $49$. Put
--
--   $$\rho_0=2+\frac9{196\sqrt{2\pi}}.$$
--
--   The outer integrand in the following convolution is integrable on $(0,\infty)$, and
--
--   $$\int_0^\infty\eta_*(w)\left(\int_{\mathbb R}\eta_+(u)\eta_+(\rho_0-w-u)\,du\right)dw
--   \ge\frac{0.8001}{49}.$$
--
--   This uses the actual band-limited smoothing and includes its signed tails. The bound transfers a compact-smoothing main-convolution estimate through a proved quantitative smoothing approximation. It provides a positive real main term for subsequent major-arc analysis. The singular-series factor and exponential-sum error estimates are separate obligations; the statement does not bound the full major-arc contribution.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, §7.2, equations (7.11)–(7.14), with the major-arc main-term role described in §3 and equation (7.24). This is an independently derived coarse lower bound for the actual etaPlus convolution, obtained from the compact main convolution and a proved L2 perturbation estimate. Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory Set

theorem Helfgott.etaPlus_etaStar_main_convolution_lower :
    IntegrableOn (fun w : ℝ => Helfgott.etaStar w*(∫ u : ℝ,
      Helfgott.etaPlus u*Helfgott.etaPlus (2+9/(196*Real.sqrt (2*Real.pi))-w-u))) (Ioi (0 : ℝ)) ∧
    (8001/490000 : ℝ) ≤
      ∫ w in Ioi (0 : ℝ), Helfgott.etaStar w*(∫ u : ℝ,
        Helfgott.etaPlus u*Helfgott.etaPlus (2+9/(196*Real.sqrt (2*Real.pi))-w-u)) := by sorry
