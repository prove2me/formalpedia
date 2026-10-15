-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_quotient_capacity_allocation
-- name    : OAI.PiExponent.LogarithmicJetIdeals.quotient_capacity_allocation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T20:34:25.949155+00:00
-- url     : https://prove2.me/theorems/c36ec987-5fde-4e27-99a6-65cd4e09c105
-- title:
--   Allocate a total within quotient capacities
-- statement:
--   If the total requested allocation is no greater than the sum of the coordinate quotient capacities, there is a finitely supported allocation totaling n that respects every coordinate capacity.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.quotient_capacity_allocation
    {m : ℕ} (e : Fin (m + 1) → ℕ) (d : Fin (m + 1) →₀ ℕ) (n : ℕ)
    (hcapacity : n ≤ ∑ i, d i / e i) :
    ∃ k : Fin (m + 1) →₀ ℕ, k.sum (fun _ x => x) = n ∧
      ∀ i, k i * e i ≤ d i := by
  sorry
