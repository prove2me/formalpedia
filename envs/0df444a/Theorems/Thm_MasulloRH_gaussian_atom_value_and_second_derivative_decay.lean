-- Prove2me | Theorems.Thm_MasulloRH_gaussian_atom_value_and_second_derivative_decay
-- name    : MasulloRH.gaussian_atom_value_and_second_derivative_decay
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T13:28:59.274822+00:00
-- url     : https://prove2.me/theorems/41fdc4c4-14c9-5e65-8119-7c052c89b283
-- title:
--   Value and second-derivative decay of a Gaussian atom with exponential argument
-- statement:
--   Let $f(x)=\exp(rx-C\exp(bx))$ and $v=C\exp(bz)$. If $|r|\le1$, $|b|\le2$, $v\ge28$ and $8rz\le v$, then $|f(z)|\le(27/10)^{-24}$ and $|f''(z)|\le161(27/10)^{-17}$. Both estimates apply to the direct and reflected theta atoms.
-- source:
--   The Masullo height-two theta-energy calculation https://prove2.me/theorems/cc487734-5ed4-5457-b10a-df505d0aef9e and its curvature-row theorem https://prove2.me/theorems/680e75e0-46e9-4f05-b70c-7f7de8530930.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv

theorem MasulloRH.gaussian_atom_value_and_second_derivative_decay (C r b z : ℝ) (hr : |r| ≤ 1) (hb : |b| ≤ 2)
    (hu : 28 ≤ C * Real.exp (b*z)) (hz : 8*(r*z) ≤ C * Real.exp (b*z)) :
    let f := fun x : ℝ => Real.exp (r*x - C*Real.exp (b*x))
    |f z| ≤ 1/(27/10:ℝ)^24 ∧ |deriv (deriv f) z| ≤ 161/(27/10:ℝ)^17 := by sorry
