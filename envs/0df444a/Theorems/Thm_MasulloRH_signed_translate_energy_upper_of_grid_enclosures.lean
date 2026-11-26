-- Prove2me | Theorems.Thm_MasulloRH_signed_translate_energy_upper_of_grid_enclosures
-- name    : MasulloRH.signed_translate_energy_upper_of_grid_enclosures
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T09:20:42.18188+00:00
-- url     : https://prove2.me/theorems/065c55b6-c5d2-48af-b68e-f303ab752328
-- title:
--   A shared grid bounds the weighted energy of a signed sum of translated functions
-- statement:
--   Let \(p,t:\mathbb R\to\mathbb C\), let \(a_i\) be finitely many complex coefficients and let the shifts be \(s_i h\) with integral \(s_i\) and grid spacing \(h\geq0\). On the cell with endpoints \(L+jh,L+(j+1)h\), enclose \(p\) in the disk with center \(P_j\) and radius \(R_j\), and bound the weight \(w\) above by \(W_j\geq0\). Enclose \(t\) on each shifted cell using the single table of centers \(T_k\) and radii \(U_k\). Set
--
--   \[
--    A_j=\left|P_j-\sum_i a_iT_{j-s_i}\right|+R_j+\sum_i |a_i|U_{j-s_i}.
--   \]
--
--   If the weighted squared residual is integrable, its integral on the first \(J\) cells is at most \(\sum_{j<J}hW_j A_j^2\). The signed sum is formed from the centers before the radii are added. Different translates can reuse the same table entry.
-- source:
--   A uniform-grid enclosure argument developed for the Masullo RH finite approximation problem. The canonical function definitions are at https://prove2.me/definitions/6f34c003-4870-4c6a-b83e-256b289a15db .

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set
open scoped BigOperators

theorem MasulloRH.signed_translate_energy_upper_of_grid_enclosures {m : ℕ} (J : ℕ) (L h : ℝ) (hh : 0 ≤ h)
    (p t : ℝ → ℂ) (w : ℝ → ℝ) (a : Fin m → ℂ) (s : Fin m → ℤ)
    (P : ℕ → ℂ) (R W : ℕ → ℝ) (T : ℤ → ℂ) (U : ℤ → ℝ) :
    let e (k : ℤ) := L + (k : ℝ) * h
    let F (x : ℝ) := w x * ‖p x - ∑ i, a i * t (x - (s i : ℝ) * h)‖ ^ 2
    let A (j : ℕ) := ‖P j - ∑ i, a i * T ((j : ℤ) - s i)‖ +
      (R j + ∑ i, ‖a i‖ * U ((j : ℤ) - s i))
    Integrable F →
    (∀ j < J, 0 ≤ W j ∧ ∀ x ∈ Icc (e j) (e ((j : ℤ) + 1)),
      ‖p x - P j‖ ≤ R j ∧ w x ≤ W j) →
    (∀ j < J, ∀ i : Fin m, ∀ z ∈ Icc (e ((j : ℤ) - s i)) (e ((j : ℤ) - s i + 1)),
      ‖t z - T ((j : ℤ) - s i)‖ ≤ U ((j : ℤ) - s i)) →
    (∫ x : ℝ in Icc L (e J), F x) ≤
      ∑ j ∈ Finset.range J, h * (W j * A j ^ 2) := by sorry
