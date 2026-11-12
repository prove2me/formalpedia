-- Prove2me | Theorems.Thm_Helfgott_etaTwo_log_expSum_quadratic_cap
-- name    : Helfgott.etaTwo_log_expSum_quadratic_cap
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T18:12:55.383752+00:00
-- url     : https://prove2.me/theorems/727e1165-e02b-4644-a78c-90c77410d095
-- title:
--   Quadratic cancellation for the actual logarithmically weighted etaTwo short sum
-- statement:
--   Let $y\ge8$ and $\theta\in\mathbb R$, and use Helfgott's actual compact smoothing $\eta_2$. Define
--   $$T_{\log}(y,\theta)=\sum_{n\ge1}\log n\,\eta_2(n/y)e(n\theta).$$
--   Away from resonance,
--   $$|T_{\log}(y,\theta)|\le\min\left\{4\log2\,\lfloor y\rfloor\log(y+2),\frac{18\log(y+2)+48\log2}{y\sin^2(\pi\theta)}\right\}.$$
--   If $\sin(\pi\theta)=0$, the first bound remains valid. This is the exact logarithmically weighted inner sum in the Vaughan Type I term, with conservative explicit constants. It does not include the outer Mobius sum or the bilinear Type II estimate.
-- source:
--   Discrete product differences applied to the actual Helfgott eta_2 smoothing in the Type I setting of Minor arcs for Goldbach, https://arxiv.org/html/1205.5252v4. Piecewise smoothing and monotonicity proofs are retained with attribution from accepted Prove2Me submission 63b25d14-2999-434f-b84f-5af50fbd02fa by raresbuhai. The first-variation, clipped-log product, weighted second-variation and quadratic Fourier bounds are new checked Lean proofs written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Definitions.Def_Helfgott_WeightedCounting
import Mathlib.Algebra.Order.Floor.Ring
open Helfgott

theorem Helfgott.etaTwo_log_expSum_quadratic_cap (y theta : ℝ) (hy : 8 ≤ y) :
    ‖expSum (fun n => ((Real.log (n:ℝ)*etaTwo ((n:ℝ)/y):ℝ):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
      if Real.sin (Real.pi*theta) = 0 then (4*Real.log 2)*(⌊y⌋₊:ℝ)*Real.log (y+2)
      else min ((4*Real.log 2)*(⌊y⌋₊:ℝ)*Real.log (y+2))
        ((18*Real.log (y+2)+48*Real.log 2)/(y*(Real.sin (Real.pi*theta))^2)) := by sorry
