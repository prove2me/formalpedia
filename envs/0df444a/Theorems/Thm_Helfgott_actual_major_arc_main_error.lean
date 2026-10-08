-- Prove2me | Theorems.Thm_Helfgott_actual_major_arc_main_error
-- name    : Helfgott.actual_major_arc_main_error
-- status  : Open
-- author  : @raresbuhai
-- created : 2026-10-05T02:40:11.712534+00:00
-- url     : https://prove2.me/theorems/56733502-57ab-4d89-9e38-5e8cb0b1eafa
-- title:
--   Coarse sufficient error for Helfgott’s actual major-arc main term
-- statement:
--   Let $N\ge10^{27}$ be odd, and put
--
--   $$\rho_0=2+\frac9{196\sqrt{2\pi}},\qquad x=\frac N{\rho_0}.$$
--
--   Let $C_0(N)$ be the actual ternary Euler constant and define the full main convolution
--
--   $$J=\int_0^\infty\eta_*(w)\int_{\mathbb R}\eta_+(u)\eta_+(\rho_0-w-u)\,du\,dw.$$
--
--   For the actual coordinated smoothing weights and Helfgott's odd/even major arcs with parameters $8$ and $150000$, prove
--
--   $$\left|\int_{\mathfrak M}S_{\eta_+}(x,\alpha)^2S_{\eta_*}(x,\alpha)e(-N\alpha)\,d\alpha-x^2C_0(N)J\right|\le0.036\frac{x^2}{49}.$$
--
--   The modulus is the complex norm. This coarser error budget, together with the actual minor-arc bound $0.97392x^2/49$, suffices for the full three-odd-prime conclusion in this large-number range. The analytic exponential-sum approximation, arc main-term identity and error estimates are obligations of this theorem. The statement does not assume these bounds.
--
--   The reference estimates its error against the compact reference convolution. The independently checked smoothing change to the full actual convolution costs at most $0.003x^2/49$, including signed tails. Thus this statement is a coarser consequence of the reference's quantitative major-arc estimate; it does not reproduce the paper's sharper numerical constant.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, §3.3, equations (3.36)–(3.38), and §7.2, equation (7.24); coordinated scale (7.14), range (7.15). The sufficient coarse error 0.036 is derived from the checked full three-prime closure; transfer from the compact reference main term is controlled by Helfgott.singular_main_convolution_perturbation. Written by Codex.

import Definitions.Def_Helfgott_ArcCounting
import Definitions.Def_Helfgott_SingularSeries
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory Set

namespace Helfgott

theorem actual_major_arc_main_error (N : ℕ) (hN : 10^27 ≤ N) (hodd : Odd N) :
    ‖(∫ α in majorArcs 8 150000 (goldbachScale N),
      ternaryIntegrand (goldbachScale N) N α ∂AddCircle.haarAddCircle)-
      (((goldbachScale N)^2*singularConstant N*(∫ w in Ioi (0:ℝ),etaStar w*(∫ u : ℝ,
        etaPlus u*etaPlus (2+9/(196*Real.sqrt (2*Real.pi))-w-u))):ℝ):ℂ)‖ ≤
        (9/250:ℝ)*((goldbachScale N)^2/49) := by sorry

end Helfgott
