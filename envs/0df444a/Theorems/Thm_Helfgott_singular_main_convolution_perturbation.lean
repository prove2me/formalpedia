-- Prove2me | Theorems.Thm_Helfgott_singular_main_convolution_perturbation
-- name    : Helfgott.singular_main_convolution_perturbation
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T02:39:25.003922+00:00
-- url     : https://prove2.me/theorems/59e82d26-7fec-4dea-8dcb-eec125a02153
-- title:
--   Uniform error between the compact and actual ternary Goldbach main terms
-- statement:
--   Let $N$ be any natural number, and let $x,\rho$ be any real numbers. For Helfgott's actual band-limited smoothing $\eta_+$ and compact reference smoothing $\eta_\circ$, put
--
--   $$J_+(\rho)=\int_0^\infty\eta_*(w)\int_{\mathbb R}\eta_+(u)\eta_+(\rho-w-u)\,du\,dw,$$
--
--   $$J_\circ(\rho)=\int_0^\infty\eta_*(w)\int_{\mathbb R}\eta_\circ(u)\eta_\circ(\rho-w-u)\,du\,dw.$$
--
--   Then the main terms differ by at most
--
--   $$\left|x^2 C_0(N)J_+(\rho)-x^2 C_0(N)J_\circ(\rho)\right|\le0.003\frac{x^2}{49}.$$
--
--   Here $C_0(N)$ is the actual convergent ternary Euler constant. The bound includes the signed tails of $\eta_+$ and is uniform in the convolution center, scale and natural argument. It permits an analytic major-arc error measured against the compact reference main term to be transferred to the full actual smoothing main term.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, §3.3 and §7.2, equations (3.36)–(3.37), (7.5), (7.9), (7.20), and (7.24). The coarser uniform perturbation 0.003 is independently derived using checked smoothing approximation and the uniform Euler upper bound 8/3. Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Definitions.Def_Helfgott_SingularSeries
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory Set

namespace Helfgott

theorem singular_main_convolution_perturbation (N : ℕ) (x ρ : ℝ) :
    ‖(((x^2*singularConstant N*(∫ w in Ioi (0:ℝ),etaStar w*
      (∫ u : ℝ,etaPlus u*etaPlus (ρ-w-u))):ℝ):ℂ))-
      (((x^2*singularConstant N*(∫ w in Ioi (0:ℝ),etaStar w*
      (∫ u : ℝ,etaCircle u*etaCircle (ρ-w-u))):ℝ):ℂ))‖ ≤
      (3/1000:ℝ)*(x^2/49) := by sorry

end Helfgott
