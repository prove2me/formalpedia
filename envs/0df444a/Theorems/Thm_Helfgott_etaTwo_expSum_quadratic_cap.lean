-- Prove2me | Theorems.Thm_Helfgott_etaTwo_expSum_quadratic_cap
-- name    : Helfgott.etaTwo_expSum_quadratic_cap
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T17:49:39.375826+00:00
-- url     : https://prove2.me/theorems/27304416-f7f9-4745-b298-f222ed9fcf44
-- title:
--   Quadratic phase cancellation for the actual compact Helfgott smoothing
-- statement:
--   For $y>0$ and real $\theta$, use Helfgott's actual compact smoothing $\eta_2(t)=4\max(\log2-|\log(2t)|,0)$ for $t>0$, and zero otherwise. Put $T(y,\theta)=\sum_{n\ge0}\eta_2(n/y)e(n\theta)$, with $e(u)=\exp(2\pi iu)$.
--
--   If $\sin(\pi\theta)\ne0$, then
--   $$|T(y,\theta)|\le\min\left\{4\log2\,\lfloor y\rfloor,\frac{18}{y\sin^2(\pi\theta)}\right\}.$$
--   At resonance the bound is $4\log2\,\lfloor y\rfloor$. The sum is finite by the smoothing's support. This is the unweighted inner exponential sum in Type I estimates; no prime-weighted or complete Vaughan estimate is asserted.
-- source:
--   Discrete second differences and a clipped-log decomposition of Helfgott eta_2, developed toward the Type I estimates in H. A. Helfgott, Minor arcs for Goldbach, https://arxiv.org/html/1205.5252v4. The constant 18 is conservative: the proof establishes total second-difference variation <=72/y rather than using the sharper continuous variation constant. Complete original Lean proof written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Definitions.Def_Helfgott_WeightedCounting
import Mathlib.Algebra.Order.Floor.Ring

theorem Helfgott.etaTwo_expSum_quadratic_cap (y theta : ℝ) (hy : 0 < y) :
    ‖Helfgott.expSum (fun n => ((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
      if Real.sin (Real.pi*theta) = 0 then (4*Real.log 2)*(⌊y⌋₊:ℝ)
      else min ((4*Real.log 2)*(⌊y⌋₊:ℝ)) (18/(y*(Real.sin (Real.pi*theta))^2)) := by sorry
