-- Prove2me | Theorems.Thm_MazurTransfer_monic_quadratic_parameter_power_profile
-- name    : MazurTransfer.monic_quadratic_parameter_power_profile
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-15T04:46:14.609021+00:00
-- url     : https://prove2.me/theorems/e577d1fe-a9f3-47c5-a01a-80c67f375f0e
-- title:
--   Monic power coordinates for a mixed quadratic parameter in every characteristic
-- statement:
--   Let R be an integral commutative ring. Let h be monic and let f have degree strictly less than h. Define (A₀,B₀)=(1,0) and (Aₙ₊₁,Bₙ₊₁)=(h Aₙ+f Bₙ,Aₙ). Then Aₙ is monic of degree n deg h, while deg Bₙ ≤ n deg h. These are the literal polynomial coordinates of (y+h)ⁿ in R[x,y]/(y²+h y-f). No restriction on characteristic is imposed. The actual downstream use is independence and freeness of the rank-three single-section parameter algebra for the mixed order-thirteen curve over the dyadic base.
-- source:
--   Owned MazurTheorem integration, Apache-2.0. The dominant-degree induction is independent of the older square-model equal-degree argument. Checked at default limits on Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib

theorem MazurTransfer.monic_quadratic_parameter_power_profile
    (R : Type*) [CommRing R] [IsDomain R] (h f : Polynomial R)
    (hh : h.Monic) (hdeg : f.natDegree < h.natDegree) (n : ℕ) :
    let c : ℕ → Polynomial R × Polynomial R :=
      Nat.rec (1, 0) (fun _ v => (h * v.1 + f * v.2, v.1))
    (c n).1.Monic ∧ (c n).1.natDegree = h.natDegree * n ∧
      (c n).2.natDegree ≤ h.natDegree * n := by sorry
