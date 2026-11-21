-- Prove2me | Theorems.Thm_NymanBeurling_localized_zero_obstruction
-- name    : NymanBeurling.localized_zero_obstruction
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:56:09.468847+00:00
-- url     : https://prove2.me/theorems/df51f7fd-a620-44fc-9d72-ea3973eb6d87
-- title:
--   Localized two-scale obstruction to a zeta zero for finite rational Bagchi certificates
-- statement:
--   Let ρ be a zero of ζ with β=Re(ρ)>1/2, ρ≠1. For finite rational coefficients let P be the squared Bagchi error on 1≤m≤H, T the true squared error on m>H, and C the usual finite certificate at any independent cutoff K. Write D=1−Σ_{m≤H} R(m)[m^(−ρ)−(m+1)^(−ρ)]. Then (2β−1)(H+1)^(2β−1)|D|² ≤ |ρ|²T and T≤C−P. In particular 2β−1 ≤ 2|ρ|² [P+(H+1)^(1−2β)(C−P)]. This detects errors confined to distant intervals even when the total certified energy grows with H.
-- source:
--   B. Bagchi, On Nyman, Beurling and Baez-Duarte’s Hilbert space reformulation of the Riemann hypothesis, https://arxiv.org/abs/math/0607733 (discrete remainder model). This localization splits the Mellin pairing at a prescribed integer.

import Mathlib

theorem NymanBeurling.localized_zero_obstruction (s : ℂ) (hs : 1/2<s.re) (h1 : s≠1) (hz : riemannZeta s=0)
    (c : ℕ→₀ℚ) (H K : ℕ) :
    let R := fun n : ℕ => 1-∑ k∈c.support,c k*((((n+1)%(k+2):ℕ):ℚ)/(k+2:ℚ))
    let E := fun n : ℕ => ((R n)^2/((n+1:ℚ)*(n+2:ℚ)):ℚ)
    let T := ∑' j : ℕ,(E (H+j):ℝ)
    let C : ℚ := (∑ n∈Finset.range K,E n)+(1+∑ k∈c.support,|c k|)^2/(K+1:ℚ)
    let D := 1-∑ n∈Finset.range H,(R n:ℂ)*((n+1:ℂ)^(-s)-(n+2:ℂ)^(-s))
    let P := ∑ n∈Finset.range H,(E n:ℝ)
    (2*s.re-1)*(H+1:ℝ)^(2*s.re-1)*‖D‖^2 ≤ T*‖s‖^2 ∧ T ≤ (C:ℝ)-P ∧
      2*s.re-1 ≤ 2*‖s‖^2*(P+(H+1:ℝ)^(1-2*s.re)*((C:ℝ)-P)) := by sorry
