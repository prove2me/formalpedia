-- Prove2me | Theorems.Thm_MasulloRH_uniform_damped_resolvent_mesh_discrepancy
-- name    : MasulloRH.uniform_damped_resolvent_mesh_discrepancy
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T12:41:18.06698+00:00
-- url     : https://prove2.me/theorems/dd67819c-16e9-4f9e-ac15-41503fe4ce53
-- title:
--   Cumulative discrepancies control the joint Euler resolvent profile uniformly in all positive damping parameters
-- statement:
--   On an increasing finite grid from zero to one with mesh at most d, let the cumulative signed mass differ from the quadratic profile u squared over two by at most epsilon. Then its damped atomic sum at every positive c differs from [1 minus (1 plus c) exp(-c)] / c squared by at most epsilon plus d. The bound is uniform even when c grows with the grid. In the rational prime cutoff application the mass increments are the normalized first prime-power contributions and the mesh is taken on logarithmic scale.
-- source:
--   Authentic critical rational Euler quotient resolvent-square trace, finite prime exhaustion at z=1+c/log P; see Masullo mission 638f9b7f-e232-4624-ba08-5889465bb1e7. This proves the arithmetic discrepancy transfer, not the operator identification.

import Mathlib
open Finset MeasureTheory

theorem MasulloRH.uniform_damped_resolvent_mesh_discrepancy (n : ℕ) (u A : ℕ → ℝ) (c d ε : ℝ)
    (hc : 0 < c) (hd : 0 ≤ d) (he : 0 ≤ ε)
    (hu : Monotone u) (hu0 : u 0 = 0) (hu1 : u n = 1) (hA : A 0 = 0)
    (hm : ∀ i < n, u (i+1) - u i ≤ d)
    (hD : ∀ i ≤ n, |A i - (u i)^2/2| ≤ ε) :
    |(∑ i ∈ range n, Real.exp (-c * u (i+1)) * (A (i+1) - A i)) -
      (1-(1+c)*Real.exp (-c))/c^2| ≤ ε+d := by sorry
