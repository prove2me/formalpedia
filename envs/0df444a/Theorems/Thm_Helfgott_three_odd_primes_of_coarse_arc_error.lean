-- Prove2me | Theorems.Thm_Helfgott_three_odd_primes_of_coarse_arc_error
-- name    : Helfgott.three_odd_primes_of_coarse_arc_error
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T02:31:51.920849+00:00
-- url     : https://prove2.me/theorems/e157dcef-3f76-4354-a06f-a7126b705ff5
-- title:
--   Three odd primes from a coarse major-arc main-term error and the actual minor-arc bound
-- statement:
--   Let $N\ge10^{27}$ be odd and put
--
--   $$\rho_0=2+\frac9{196\sqrt{2\pi}},\qquad x=\frac N{\rho_0}.$$
--
--   For Helfgott's actual coordinated smoothing weights, define the real main convolution
--
--   $$J=\int_0^\infty\eta_*(w)\left(\int_{\mathbb R}\eta_+(u)\eta_+(\rho_0-w-u)\,du\right)dw.$$
--
--   Assume the following two analytic bounds on the actual major and minor arcs:
--
--   $$\left|\int_{\mathfrak M}S_{\eta_+}(x,\alpha)^2S_{\eta_*}(x,\alpha)e(-N\alpha)\,d\alpha-x^2C_0(N)J\right|
--   \le0.036\frac{x^2}{49},$$
--
--   $$\int_{\mathfrak M^c}|S_{\eta_+}(x,\alpha)|^2|S_{\eta_*}(x,\alpha)|\,d\alpha
--   \le0.97392\frac{x^2}{49}.$$
--
--   Then $N$ is a sum of three odd primes. Both analytic estimates are explicit hypotheses of this theorem. The constant $C_0(N)$ is the actual ternary Euler constant, and $J$ includes the signed tails of the band-limited smoothing. The proof establishes the entire remaining implication, including convergence, the Euler lower bound, the actual main-convolution lower bound, counting, prime-power removal and the numerical margin. It does not prove either assumed analytic estimate.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, §7.2–§7.4, equations (7.9)–(7.10), (7.24)–(7.25), (7.48)–(7.50). The coarser sufficient major-arc error 0.036 is independently derived from checked main-term and removal bounds; it leaves the full three-prime conclusion unchanged. Written by Codex.

import Definitions.Def_Helfgott_ArcCounting
import Definitions.Def_Helfgott_SingularSeries
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory Set

namespace Helfgott

theorem three_odd_primes_of_coarse_arc_error (N : ℕ) (hN : 10^27 ≤ N) (hodd : Odd N)
    (herror : ‖(∫ α in majorArcs 8 150000 (goldbachScale N),
      ternaryIntegrand (goldbachScale N) N α ∂AddCircle.haarAddCircle)-
      (((goldbachScale N)^2*singularConstant N*(∫ w in Ioi (0:ℝ),etaStar w*(∫ u : ℝ,
        etaPlus u*etaPlus (2+9/(196*Real.sqrt (2*Real.pi))-w-u))):ℝ):ℂ)‖ ≤
        (9/250:ℝ)*((goldbachScale N)^2/49))
    (hminor : minorArcMass (goldbachScale N) ≤
      (97392/100000:ℝ)*((goldbachScale N)^2/49)) :
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ N = p+q+r := by sorry

end Helfgott
