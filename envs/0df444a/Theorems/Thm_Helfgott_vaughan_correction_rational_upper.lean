-- Prove2me | Theorems.Thm_Helfgott_vaughan_correction_rational_upper
-- name    : Helfgott.vaughan_correction_rational_upper
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T18:04:47.976609+00:00
-- url     : https://prove2.me/theorems/0d1c4493-c30c-465e-8099-3473b2837b82
-- title:
--   An explicit rational-approximation bound for the actual Vaughan correction sum
-- statement:
--   Let $U,V$ be natural cutoffs, $y>0$, $q\ge2$, $(|a|,q)=1$, and $\theta=a/q+\beta$ with $|\beta|\le q^{-2}$. Put $B=\min(UV,\lfloor y\rfloor)$ and
--   $$c=(\mu\,1_{[1,U]})*(\Lambda\,1_{[1,V]})*1,$$
--   where the products are Dirichlet convolutions. For Helfgott's actual compact smoothing $\eta_2$,
--   $$\left|\sum_{n\ge0}c(n)\eta_2(n/y)e(n\theta)\right|
--   \le\log(B+q)\left(\frac{9q^4}{y}+\frac{24y}{q}(1+\log(B+q))+30(B+q)\right).$$
--   The estimate covers all positive scales and cutoffs, including odd denominators, exact resonances, and a final partial block. The constants are conservative; this bounds the correction term alone and does not assert the full prime exponential-sum estimate.
-- source:
--   Classical Vaughan decomposition, rational spacing, and second-difference estimates, in the setting of H. A. Helfgott, Minor arcs for Goldbach, https://arxiv.org/html/1205.5252v4. The finite arithmetic decomposition is retained with attribution from accepted Prove2Me submission 63b25d14-2999-434f-b84f-5af50fbd02fa by raresbuhai; rational-grid spacing is retained with attribution from submission 968ef56d-d4b0-42b8-99aa-5a18c7253fab by marwahaha, with its Apache 2.0 attribution to Gershon Bialer. The quadratic smoothing, small-divisor, block summation and explicit global bound are new checked Lean proofs written by Codex.

import Definitions.Def_Helfgott_VaughanData
import Mathlib.Algebra.Order.Floor.Ring
open Helfgott

theorem Helfgott.vaughan_correction_rational_upper (U V q : ℕ) (a : ℤ) (y theta beta : ℝ)
    (hy : 0 < y) (hq : 2 ≤ q) (haq : Nat.Coprime a.natAbs q)
    (htheta : theta = (a:ℝ)/(q:ℝ)+beta) (hbeta : |beta| ≤ 1/(q:ℝ)^2) :
    let B := min (U*V) ⌊y⌋₊
    ‖expSum (fun n => ((vaughanCorrection U V n*etaTwo ((n:ℝ)/y):ℝ):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
      Real.log (B+q:ℕ)*(9*(q:ℝ)^4/y+
        24*y/(q:ℝ)*(1+Real.log (B+q:ℕ))+30*(B+q:ℕ)) := by sorry
