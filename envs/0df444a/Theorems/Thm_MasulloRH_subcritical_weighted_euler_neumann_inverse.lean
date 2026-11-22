-- Prove2me | Theorems.Thm_MasulloRH_subcritical_weighted_euler_neumann_inverse
-- name    : MasulloRH.subcritical_weighted_euler_neumann_inverse
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T12:18:54.517177+00:00
-- url     : https://prove2.me/theorems/4a5e1993-1338-4968-97bb-436b24652bf1
-- title:
--   The weighted half-twist Euler difference has a two-sided Neumann inverse below critical width
-- statement:
--   For the square root of the physical Gram weight $e^{α|x|}(1+x²)$, a log shift $L>0$ and $0≤α<1/2$, the supremum over positions of the exact weight ratio for the nth damped shift is a summable sequence. Any bounded Hilbert or Banach operator satisfying this power estimate has absolutely summable powers, whose sum inverts its Euler difference on both sides.
-- source:
--   Masullo (9.2.2.41), half-twist p-Euler layer (11.3.1.3), comparison with the critical-layer analysis in mission 638f9b7f-e232-4624-ba08-5889465bb1e7.

import Mathlib
open Filter Topology

theorem MasulloRH.subcritical_weighted_euler_neumann_inverse (α L : ℝ) (ha : 0 ≤ α) (hc : α < 1/2) (hL : 0 < L) :
    let w := fun x : ℝ => Real.exp (α * |x|) * (1 + x^2)
    let b := fun n : ℕ => sSup (Set.range (fun x : ℝ =>
      Real.exp (-(n:ℝ)*L/2) * w x / w (x+(n:ℝ)*L)))
    Summable b ∧ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (T : E →L[ℝ] E), (∀ n : ℕ, ‖T^n‖ ≤ b n) →
      Summable (fun n : ℕ => ‖T^n‖) ∧
      (1-T)*(∑' n : ℕ, T^n) = 1 ∧ (∑' n : ℕ, T^n)*(1-T) = 1 := by sorry
