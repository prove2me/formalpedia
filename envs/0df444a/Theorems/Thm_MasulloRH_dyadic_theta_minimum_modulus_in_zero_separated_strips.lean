-- Prove2me | Theorems.Thm_MasulloRH_dyadic_theta_minimum_modulus_in_zero_separated_strips
-- name    : MasulloRH.dyadic_theta_minimum_modulus_in_zero_separated_strips
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T03:53:52.837338+00:00
-- url     : https://prove2.me/theorems/a7956349-57df-4ddd-add5-5b2029cc546a
-- title:
--   A quantitative minimum-modulus bound for the dyadic completed zeta factor in an interior strip
-- statement:
--   Write G(s)=(1−2^(−s))(1−2^(1−s))Λ(s). On any fixed closed substrip of 0<Re(s)<1, suppose the point s is at least d/(1+|Im(s)|)^A from every nontrivial zeta zero whose ordinate is within 3. Then G(s) is nonzero and log⁺(1/|G(s)|)≤D(1+|Im(s)|)², for a constant uniform over all such points. The bound needs no spacing between the zeros.
-- source:
--   Analytic input for Masullo’s rational spectral synthesis, §§9–10. Local Blaschke lemmas adapted from the Apache-2.0 PrimeNumberTheoremAnd project, StrongPNT.lean, and the Zeta23 port. https://github.com/AlexKontorovich/PrimeNumberTheoremAnd

import Mathlib
open scoped Topology

theorem MasulloRH.dyadic_theta_minimum_modulus_in_zero_separated_strips (a b : ℝ) (ha : 0<a) (hb : b<1) (d : ℝ) (hd : 0<d) (A : ℕ) :
    let G := fun s : ℂ => (1-(2:ℂ)^(-s))*(1-(2:ℂ)^(1-s))*completedRiemannZeta s
    ∃ D : ℝ, 0<D ∧ ∀ s : ℂ, a ≤ s.re → s.re≤b →
      (∀ ρ : ℂ, riemannZeta ρ=0 → 0<ρ.re → ρ.re<1 → |ρ.im-s.im|≤3 →
        d/(1+|s.im|)^A≤‖s-ρ‖) →
      G s≠0 ∧ max 0 (-Real.log ‖G s‖)≤D*(1+|s.im|)^2 := by sorry
