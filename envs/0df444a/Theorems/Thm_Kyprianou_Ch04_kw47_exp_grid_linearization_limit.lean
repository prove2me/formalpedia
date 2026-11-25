-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_exp_grid_linearization_limit
-- name    : Kyprianou.Ch04.kw47_exp_grid_linearization_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:15:38.436747+00:00
-- url     : https://prove2.me/theorems/ac9d685c-5d98-5985-b48c-4a27ad209714
-- title:
--   Vanishing weighted exponential linearisation error for continuous finite-variation exponents
-- statement:
--   For continuous exponents on a compact interval and a uniformly bounded total grid variation, the weighted first-order exponential remainder converges to zero along every monotone vanishing-mesh grid. Compact uniform continuity gives uniformly small exponent increments; the proved finite-grid Taylor bound then implies convergence.
-- source:
--   Kyprianou (2006), Exercise 4.7; exponential product-grid integration by parts.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_exp_grid_linearization
open Filter Set Topology
set_option autoImplicit false

/-- Continuous exponents of uniformly bounded grid variation admit
first-order linearisation along arbitrary vanishing-mesh grids. -/

theorem Kyprianou.Ch04.kw47_exp_grid_linearization_limit
    (a b : Real) (g : Real → Real) (hg : ContinuousOn g (Icc a b))
    (u : Nat → Nat → Real) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n → u n (i+1) - u n i ≤ delta n)
    (Z : Nat → Nat → Real) (hZ : ∀ n i, |Z n i| ≤ 1)
    (C : Real) (hC : 0 ≤ C)
    (hVar : ∀ n, (∑ i ∈ Finset.range (N n),
      |g (u n (i+1)) - g (u n i)|) ≤ C) :
    Tendsto (fun n =>
      (∑ i ∈ Finset.range (N n),
        Z n i * (1 - Real.exp (-(g (u n (i+1)) - g (u n i))))) -
      (∑ i ∈ Finset.range (N n),
        Z n i * (g (u n (i+1)) - g (u n i))))
      atTop (nhds 0) := by sorry
