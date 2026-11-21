-- Prove2me | Theorems.Thm_NymanBeurling_periodic_remainder_mean_square_gcd
-- name    : NymanBeurling.periodic_remainder_mean_square_gcd
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:51:57.226146+00:00
-- url     : https://prove2.me/theorems/94aae205-5c7a-4147-9ce2-7a8a3af2f381
-- title:
--   Exact gcd formula for the mean square and the distant tail of a finite Bagchi residual
-- statement:
--   For arbitrary real coefficients on a finite set S of positive denominators, put R(m)=1−Σ_d c_d (m mod d)/d. For every common positive period P the mean of R(m)² over one period is exactly M = [1−Σ_d c_d(d−1)/(2d)]² + Σ_{d,e} c_d c_e (gcd(d,e)²−1)/(12de). Moreover, (H+1) times the Bagchi energy in m>H converges to this same M. The coefficients are fixed while H tends to infinity. The result gives the exact leading constant, including the arithmetic correlations between denominators.
-- source:
--   B. Bagchi, On Nyman, Beurling and Baez-Duarte’s Hilbert space reformulation of the Riemann hypothesis, https://arxiv.org/abs/math/0607733 (discrete fractional-part model and its norm). The finite discrete covariance and weighted tail formula are derived here.

import Mathlib

open Filter Topology

theorem NymanBeurling.periodic_remainder_mean_square_gcd (S : Finset ℕ) (c : ℕ→ℝ) (P : ℕ) (hP : 0<P)
    (hd : ∀ d∈S,0<d) (hper : ∀ d∈S,d∣P) :
    let R := fun m : ℕ => 1-∑ d ∈ S,c d*((m%d:ℕ):ℝ)/(d:ℝ)
    let M := (1-∑ d ∈ S,c d*((d:ℝ)-1)/(2*d))^2+
      ∑ d ∈ S,∑ e ∈ S,c d*c e*((d.gcd e:ℝ)^2-1)/(12*d*e)
    (∑ m ∈ Finset.range P,(R m)^2)/(P:ℝ)=M ∧
      Tendsto (fun H : ℕ => (H+1:ℝ)*∑' j : ℕ,
        (R (H+j+1))^2/(((H+j:ℕ)+1:ℝ)*((H+j:ℕ)+2:ℝ))) atTop (𝓝 M) := by sorry
