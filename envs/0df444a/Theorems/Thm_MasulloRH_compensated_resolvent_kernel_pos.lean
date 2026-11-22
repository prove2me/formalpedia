-- Prove2me | Theorems.Thm_MasulloRH_compensated_resolvent_kernel_pos
-- name    : MasulloRH.compensated_resolvent_kernel_pos
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-22T00:00:45.625827+00:00
-- url     : https://prove2.me/theorems/0d330867-c0fb-4459-8251-656184ea7256
-- title:
--   Compensated shifted resolvent is positive at high zero height
-- statement:
--   Let $\rho=\beta+i\gamma$ with $0\le\beta\le1$ and $\gamma^2\ge36$. Put $a=3-\beta$, $b=5/2-\beta$, and $c_0=\operatorname{Re}((3-\rho)^{-1}-(5/2-\rho)^{-1})=a/(a^2+\gamma^2)-b/(b^2+\gamma^2)$. For a real probe height $T$, define
--
--   $$k_T(\rho)=\frac{a}{a^2+(T-\gamma)^2}-\frac{b}{b^2+\gamma^2}+8c_0.$$
--
--   Then $k_T(\rho)>0$ and
--
--   $$\frac{a}{a^2+(T-\gamma)^2}\le k_T(\rho).$$
--
--   This is the elementary high-height sign estimate for the compensated shifted-resolvent route to Masullo's regularized trace lower bound. It is only an arithmetic certificate; it does not assert a trace inequality or any zero-location statement.
-- source:
--   Masullo, The Music of the Primes, §§1.4.2–1.4.5 and Theorem 12.5.1.1 (20 November 2026 draft), together with the compensated-resolvent proposal in the Prove2Me Masullo mission discussion, comment ad8fb92e-0c03-4bee-937c-638f829135a3.

import Mathlib

theorem MasulloRH.compensated_resolvent_kernel_pos (β γ T : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hγ : 36 ≤ γ ^ 2) :
    let a := 3 - β
    let b := 5 / 2 - β
    let c0 := a / (a ^ 2 + γ ^ 2) - b / (b ^ 2 + γ ^ 2)
    let k := a / (a ^ 2 + (T - γ) ^ 2) - b / (b ^ 2 + γ ^ 2) + 8 * c0
    0 < k ∧ a / (a ^ 2 + (T - γ) ^ 2) ≤ k := by sorry
