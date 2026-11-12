-- Prove2me | Theorems.Thm_Helfgott_vaughan_typeOne_rational_upper
-- name    : Helfgott.vaughan_typeOne_rational_upper
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T18:24:35.65721+00:00
-- url     : https://prove2.me/theorems/c0f032cc-9576-460a-ab3b-3fb8290fe006
-- title:
--   A complete explicit rational bound for the logarithmic Vaughan Type I sum
-- statement:
--   Let $U$ be a natural cutoff, $y\ge8$, $8U\le y$, $q\ge2$, $(|a|,q)=1$, and $\theta=a/q+\beta$ with $|\beta|\le q^{-2}$. Let $a_U=(\mu 1_{[1,U]})*\log$, where $*$ is Dirichlet convolution. For Helfgott's compact smoothing $\eta_2$,
--   $$\left|\sum_{n\ge1}a_U(n)\eta_2(n/y)e(n\theta)\right|\le4\log(y+2)\left(\frac{9q^4}{y}+\frac{24y}{q}(1+\log(U+q))+30(U+q)\right).$$
--   This gives an unconditional explicit bound for the complete logarithmic Type I term in Vaughan's decomposition. The constants are conservative, and the estimate does not itself assert the full prime exponential-sum bound.
-- source:
--   Classical Vaughan decomposition and rational spacing in the setting of H. A. Helfgott, Minor arcs for Goldbach, https://arxiv.org/html/1205.5252v4. Finite arithmetic identities retained with attribution from accepted submission 63b25d14-2999-434f-b84f-5af50fbd02fa by raresbuhai; rational spacing retained from 968ef56d-d4b0-42b8-99aa-5a18c7253fab by marwahaha with Apache 2.0 attribution to Gershon Bialer. Logarithmic second variation, quadratic bounds, and complete outer summation proved by Codex.

import Definitions.Def_Helfgott_VaughanData
open Helfgott

theorem Helfgott.vaughan_typeOne_rational_upper (U q : ℕ) (a : ℤ) (y theta beta : ℝ)
    (hy : 8 ≤ y) (hU : 8*(U:ℝ) ≤ y) (hq : 2 ≤ q) (haq : Nat.Coprime a.natAbs q)
    (htheta : theta = (a:ℝ)/(q:ℝ)+beta) (hbeta : |beta| ≤ 1/(q:ℝ)^2) :
    ‖expSum (fun n => ((vaughanTypeOne U n*etaTwo ((n:ℝ)/y):ℝ):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
      (4*Real.log (y+2))*(9*(q:ℝ)^4/y+
        24*y/(q:ℝ)*(1+Real.log (U+q:ℕ))+30*(U+q:ℕ)) := by sorry
