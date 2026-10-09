-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_frozen_prefix_rebuild
-- name    : NestedSeatAlloc.IntPolicy.revenue_frozen_prefix_rebuild
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T14:15:46.713185+00:00
-- url     : https://prove2.me/theorems/dcb8685b-7f41-4b5d-a642-9d9890b31e69
-- title:
--   Frozen next-class revenue equals the reconstruction from higher-fare prefix and frozen demand
-- statement:
--   # The frozen revenue path equals the finite-prefix reconstructed path
--
--   Nested revenue through class k+1 reads only demand entries at indices
--   1,...,k+1. For all i<=k, the frozen path created by Function.update at
--   k+1 agrees with the stored prefix vector U(ω)(i)=X_i(ω). At i=k+1,
--   both the frozen path and prefixRevenueRebuild k read the chosen frozen
--   demand value y. Values outside this prefix are irrelevant to revenue.
--
--   The Proved revenue_extensional_on_prefix theorem converts these
--   pointwise index equalities to the equality of revenue f p ... (k+1) s.
--   The proof splits at i=k+1, using Finset.Icc bounds for the other
--   indices, and then simp with the official prefixRevenueRebuild definition.
--
--   This exact identity is the hUpdate premise in the Proved
--   condRevenue_eq_integral_prefix_law (ece4ad20-ded2-4a30-ac70-92b03f6becb3).
--   It is needed to replace the abstract reconstruction used in the
--   independence/product-law proof with the real NestedSeatAlloc model.
--
--   No local Lean or Lake is used. Accepted remote compilation is required.
-- source:
--   # The frozen revenue path equals the finite-prefix reconstructed path
--
--   Nested revenue through class k+1 reads only demand entries at indices
--   1,...,k+1. For all i<=k, the frozen path created by Function.update at
--   k+1 agrees with the stored prefix vector U(ω)(i)=X_i(ω). At i=k+1,
--   both the frozen path and prefixRevenueRebuild k read the chosen frozen
--   demand value y. Values outside this prefix are irrelevant to revenue.
--
--   The Proved revenue_extensional_on_prefix theorem converts these
--   pointwise index equalities to the equality of revenue f p ... (k+1) s.
--   The proof splits at i=k+1, using Finset.Icc bounds for the other
--   indices, and then simp with the official prefixRevenueRebuild definition.
--
--   This exact identity is the hUpdate premise in the Proved
--   condRevenue_eq_integral_prefix_law (ece4ad20-ded2-4a30-ac70-92b03f6becb3).
--   It is needed to replace the abstract reconstruction used in the
--   independence/product-law proof with the real NestedSeatAlloc model.
--
--   No local Lean or Lake is used. Accepted remote compilation is required.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_prefixRevenueRebuild
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.revenue_frozen_prefix_rebuild
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (k : ℕ)
    (ω : Ω) (y s : ℝ) :
    revenue f p (Function.update (fun i => X i ω) (k + 1) y) (k + 1) s =
    revenue f p
      (prefixRevenueRebuild k (y, fun i : (Finset.Icc 1 k) => X i.1 ω))
      (k + 1) s := by sorry
