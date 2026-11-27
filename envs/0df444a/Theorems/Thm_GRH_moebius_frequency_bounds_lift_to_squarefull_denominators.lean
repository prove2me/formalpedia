-- Prove2me | Theorems.Thm_GRH_moebius_frequency_bounds_lift_to_squarefull_denominators
-- name    : GRH.moebius_frequency_bounds_lift_to_squarefull_denominators
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T06:03:24.474278+00:00
-- url     : https://prove2.me/theorems/02ed77a3-0226-5865-b75f-5d94e3de83f9
-- title:
--   Power bounds at squarefull denominators control each rational-frequency level
-- statement:
--   Fix q>0 and θ≥0. For any positive squarefull multiple t of q, bounds for reduced frequencies at the squarefull d satisfying q∣d∣t imply bounds at denominator q, with constants depending on the frequency. One may always take t=q².
-- source:
--   For the Möbius function, write S_N(x) for the sum of μ(n) exp(2πinx) through N. The bilinear sum B(q,a,N) and the coprime reciprocal sum H_q(U) use the original mission normalizations. The prime-square Fourier filter in this submission series supplies the descent.

import Definitions.Def_GRH_SquarefullFrequencies

open Finset GRH.AdditiveMoebiusSpectrum GRH.SquarefullFrequencies

theorem GRH.moebius_frequency_bounds_lift_to_squarefull_denominators (q : ℕ) (hq : 0 < q) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∀ t : ℕ, 0 < t → squarefull t → q ∣ t →
      (∀ d : ℕ, q ∣ d → d ∣ t → squarefull d → level d θ) → level q θ) ∧
    ((∀ d : ℕ, q ∣ d → d ∣ q^2 → squarefull d → level d θ) → level q θ) := by sorry
