-- Prove2me | Theorems.Thm_Kyprianou_Ch04_uniformGridSingleAtomLimitV1
-- name    : Kyprianou.Ch04.uniformGridSingleAtomLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:15:25.170168+00:00
-- url     : https://prove2.me/theorems/d0316c1e-4882-57d5-80cc-0ebaaba36813
-- title:
--   Uniform grid single atom strict-left limit
-- statement:
--   Use uniqueness of the right-closed uniform cell to reduce the sum to a single strict-left sample, then compose left-limit convergence with the cell approach.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal Classical
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem uniformGridSingleAtomLimitV1 (T r : NNReal) (H : NNReal → ℝ)
    (k : ℕ → ℕ) (hk : ∀ n, k n < n+1)
    (hc : ∀ n, T * (k n : NNReal) / ((n+1 : ℕ) : NNReal) < r ∧
      r ≤ T * ((k n+1 : ℕ) : NNReal) / ((n+1 : ℕ) : NNReal))
    (hH : Tendsto H (𝓝[<] r) (𝓝 (H r))) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n+1),
      if T * (i : NNReal) / ((n+1 : ℕ) : NNReal) < r ∧
        r ≤ T * ((i+1 : ℕ) : NNReal) / ((n+1 : ℕ) : NNReal)
      then H (T * (i : NNReal) / ((n+1 : ℕ) : NNReal)) else 0)
      atTop (𝓝 (H r)) := by
  sorry
end Kyprianou.Ch04
