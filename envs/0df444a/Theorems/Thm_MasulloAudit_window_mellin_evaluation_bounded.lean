-- Prove2me | Theorems.Thm_MasulloAudit_window_mellin_evaluation_bounded
-- name    : MasulloAudit.window_mellin_evaluation_bounded
-- status  : Proved
-- author  : @deleted
-- created : 2026-11-21T00:27:50.032124+00:00
-- url     : https://prove2.me/theorems/e2170362-8fa5-4c24-b4ab-c9ae6809338e
-- title:
--   Mellin evaluation is bounded on the window space $L^2(e^{2\alpha|u|}du)$ for $|\operatorname{Re}z|<\alpha$
-- statement:
--   Let $\alpha>0$ and $z\in\mathbf C$ with $|\operatorname{Re}z|<\alpha$, and write $c=\operatorname{Re}z$. Then
--
--   $$
--   \int_{\mathbf R}e^{2cu-2\alpha|u|}\,du=\frac1{2(\alpha-c)}+\frac1{2(\alpha+c)}=\frac{\alpha}{\alpha^2-c^2}<\infty,
--   $$
--
--   and for every measurable $g:\mathbf R\to\mathbf C$,
--
--   $$
--   \Bigl(\int_{\mathbf R}|g(u)|\,|e^{zu}|\,du\Bigr)^2\le\frac{\alpha}{\alpha^2-c^2}\int_{\mathbf R}|g(u)|^2e^{2\alpha|u|}\,du .
--   $$
--
--   In logarithmic coordinates $u=\log x$, the Hardy–Sobolev space $W_I^0$ of Masullo's draft with window $I=[-\alpha,\alpha]$ (Def. 9.2.2.1, p. 412, with the norm in the form (9.2.2.4) of Lemma 9.2.2.2; (1.8.2.2), p. 44) is the weighted space $L^2(\mathbf R,e^{2\alpha|u|}du)$. The Mellin evaluation $g\mapsto\int g(u)e^{zu}\,du$ is then a bounded functional on it whenever $|\operatorname{Re}z|<\alpha$. This is the mechanism by which zeros with $|\operatorname{Re}\rho-\tfrac12|<\alpha$ become visible on the window space. The companion theorem `MasulloAudit.window_mellin_evaluation_edge_unbounded` shows that boundedness fails at $|\operatorname{Re}z|=\alpha$.
--
--   **Formalization Note.** The inequality is stated with lower Lebesgue integrals (`lintegral`) and extended norms. The weight integral is given both as a Bochner integral and as a `lintegral`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, (1.8.2.2) p. 44, Def. 9.2.2.1, Thm 10.4.2.8.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false

open MeasureTheory Set

namespace MasulloAudit

/-- Window Mellin evaluation (log coordinates). On the Hardy–Sobolev window space
`L²(ℝ, e^{2α|u|} du)` the evaluation `g ↦ ∫ g(u) e^{zu} du` is bounded when `|Re z| < α`:
the weight `e^{2 Re z · u − 2α|u|}` is integrable with integral
`1/(2(α − Re z)) + 1/(2(α + Re z))`, and by Cauchy–Schwarz
`(∫ |g| |e^{zu}|)² ≤ C · ∫ |g|² e^{2α|u|}` with that constant `C`. -/
theorem window_mellin_evaluation_bounded (α : ℝ) (_hα : 0 < α) (z : ℂ) (hz : |z.re| < α) :
    Integrable (fun u : ℝ => Real.exp (2 * z.re * u - 2 * α * |u|)) ∧
    (∫ u : ℝ, Real.exp (2 * z.re * u - 2 * α * |u|)) =
      1 / (2 * (α - z.re)) + 1 / (2 * (α + z.re)) ∧
    (∫⁻ u : ℝ, ENNReal.ofReal (Real.exp (2 * z.re * u - 2 * α * |u|))) =
      ENNReal.ofReal (1 / (2 * (α - z.re)) + 1 / (2 * (α + z.re))) ∧
    ∀ g : ℝ → ℂ, Measurable g →
      (∫⁻ u : ℝ, ‖g u‖ₑ * ‖Complex.exp (z * u)‖ₑ) ^ 2 ≤
        ENNReal.ofReal (1 / (2 * (α - z.re)) + 1 / (2 * (α + z.re))) *
          ∫⁻ u : ℝ, ‖g u‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * α * |u|)) := by sorry

end MasulloAudit
