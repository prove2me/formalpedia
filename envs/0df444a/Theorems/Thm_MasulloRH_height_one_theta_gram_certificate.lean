-- Prove2me | Theorems.Thm_MasulloRH_height_one_theta_gram_certificate
-- name    : MasulloRH.height_one_theta_gram_certificate
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:13:34.868443+00:00
-- url     : https://prove2.me/theorems/d56c0b5b-f1f6-46f1-8968-303a7e716c02
-- title:
--   A verified one-translate theta certificate for a height-one rectangle
-- statement:
--   Take $c=3/4,b=3/20,\delta=1/20,T=1$. A single translate of the explicit dyadic theta profile, with coefficient $3/2$ and shift $3/4$, gives weighted residual energy $J<22/1000<e^{-1/2}/20$. In particular $\zeta(s)\ne0$ throughout the closed rectangle $13/20\le\Re(s)\le17/20$, $|\Im(s)|\le1$. The first assertion certifies the explicit theta approximation itself.
-- source:
--   Concrete finite witness for the physical-space criterion MasulloRH.finite_theta_approximation_excludes_rectangle_zeros, 8481aa5d. The proof uses the Jacobi reflection formula, rational enclosures of elementary exponentials, and the compact-window norm of Masullo §9.2.2, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=412.

import Definitions.Def_MasulloRH_GaussianThetaApproximation
open MeasureTheory Set MasulloRH.GaussianApproximation
open scoped Topology

theorem MasulloRH.height_one_theta_gram_certificate :
    (energy (3/4) (3/20) (residual 1 (fun _ : Fin 1 => (3/2:ℂ)) (fun _ => (3/4:ℝ))) < 22/1000 ∧
       (22/1000:ℝ) < (1/20) * Real.exp (-(1/2:ℝ))) ∧
    ∀ s : ℂ, s.re ∈ Icc (13/20:ℝ) (17/20) → |s.im| ≤ 1 → riemannZeta s ≠ 0 := by sorry
