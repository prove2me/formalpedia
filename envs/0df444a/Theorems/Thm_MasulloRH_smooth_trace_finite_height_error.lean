-- Prove2me | Theorems.Thm_MasulloRH_smooth_trace_finite_height_error
-- name    : MasulloRH.smooth_trace_finite_height_error
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:24:32.649011+00:00
-- url     : https://prove2.me/theorems/eeb3057a-b84c-4114-9aec-7cd81ab33eba
-- title:
--   Uniform finite-height error for Masullo’s smooth-test explicit formula, with an Euler-derivative bound of every order
-- statement:
--   Let $\varphi$ be an admissible smooth compactly supported test on $\mathbb R_{>0}$ with $\varphi(1)=0$. Let $G(\varphi)$ be the real-place integral plus the prime-power sum in the rational trace formula. For a nontrivial zero $\rho=\beta+i\gamma$ put $t_\rho=m_\rho\mathcal M\varphi(\rho-1/2)$. Let $S_\alpha$ sum $t_\rho$ over $|\beta-1/2|<\alpha$, and $O_{\alpha,H}$ sum it over the omitted zeros with $|\gamma|\le H$. For $k,n\ge0$, put $H=5/2+2n$, $D=t\,d/dt$, and
--   $$B_j(\varphi)=\int_0^\infty(t^{-3/2}+t^{-1/2})\,|D^j\varphi(t)|\,dt.$$
--   Write $A$ for the full reference resolvent mass at 3 and $L=\zeta'/\zeta$. Then, uniformly in the window half-width $\alpha$,
--   $$\left|\mathcal M\varphi(1/2)+\mathcal M\varphi(-1/2)-G(\varphi)-S_\alpha-O_{\alpha,H}\right|\le\frac{2B_{k+2}(\varphi)}{H^k}\frac{2}{H-1}\left(8A-\Re L(5/2)+\frac{1+\log n}{2}\right).$$
--   The convention for $n=0$ is $\log 0=0$. The correction uses only zeros through the stated height. The error decreases faster than every fixed inverse power for a fixed smooth test.
-- source:
--   Quantitative companion to the rational specialization of Masullo, Theorem 12.5.1.1, using the proved full-strip explicit formula, weighted-zero summability, and the verified logarithmic height-tail estimate 7bc6a754. The Euler-derivative bound is proved directly by integration by parts.

import Definitions.Def_MasulloRH_RegularizedTrace

set_option autoImplicit false

open MeasureTheory Set

namespace MasulloRH

theorem smooth_trace_finite_height_error (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ)
    (α : ℝ) (n k : ℕ) :
    let H : ℝ := 5/2+2*n
    let D : (ℝ → ℂ) → ℝ → ℂ := fun f t => (t:ℂ)*deriv f t
    let B := ∫ t in Ioi (0:ℝ), (t^(-3/2:ℝ)+t^(-1/2:ℝ))*‖(D^[k+2] φ) t‖
    ‖(mellin φ (1/2) + mellin φ (-1/2) -
       ((∫ t in Ioi (1:ℝ),realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i))) -
       (∑' z : ZetaZerosInTraceStrip α,zetaTraceTerm φ α z) -
       (∑' z : ZetaZerosInTraceStrip (1/2),if α ≤ |z.val.re-1/2| ∧ |z.val.im| ≤ H
         then zetaTraceTerm φ (1/2) z else 0)‖ ≤
    (2*B/H^k) * (2/(H-1) * (8*((zetaLogDeriv 3).re -
      (zetaLogDeriv (5/2)+regularizedArch 3-regularizedPolar 3).re) -
      (zetaLogDeriv (5/2)).re + (1+Real.log n)/2)) := by sorry

end MasulloRH
