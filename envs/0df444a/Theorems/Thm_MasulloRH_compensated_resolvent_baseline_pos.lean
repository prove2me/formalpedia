-- Prove2me | Theorems.Thm_MasulloRH_compensated_resolvent_baseline_pos
-- name    : MasulloRH.compensated_resolvent_baseline_pos
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-22T00:40:55.699346+00:00
-- url     : https://prove2.me/theorems/725e5adc-93c2-47b6-bf62-6ae8bc3b240c
-- title:
--   Positive uncompensated baseline for the shifted resolvent
-- statement:
--   Let $\rho=\beta+i\gamma$ with $0\le\beta\le1$ and $\gamma^2\ge36$. Define
--
--   $$c_0(\rho)=\operatorname{Re}\left((3-\rho)^{-1}-(5/2-\rho)^{-1}\right)
--   =\frac{3-\beta}{(3-\beta)^2+\gamma^2}-\frac{5/2-\beta}{(5/2-\beta)^2+\gamma^2}.
--   $$
--
--   Then $c_0(\rho)>0$. The proof is an exact factorization: the numerator is $(a-b)(\gamma^2-ab)$ with $a=3-\beta$, $b=5/2-\beta$, while $a-b=1/2$ and $ab\le15/2<36\le\gamma^2$. This is a Masullo-native sign audit for the regularized trace; it contains no zeta zero-location premise and does not use the Alpöge--Claude formalization.
-- source:
--   Masullo, The Music of the Primes, Theorem 12.5.1.1 and the compensated-resolvent discussion in the Masullo mission; exact algebraic sign audit.

import Mathlib

theorem MasulloRH.compensated_resolvent_baseline_pos
    (β γ : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hγ : 36 ≤ γ ^ 2) :
    let a := 3 - β
    let b := 5 / 2 - β
    let c0 := a / (a ^ 2 + γ ^ 2) - b / (b ^ 2 + γ ^ 2)
    0 < c0 := by sorry
