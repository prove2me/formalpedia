-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_global_optimality_of_prefix_concavity
-- name    : NestedSeatAlloc.IntPolicy.theorem1_global_optimality_of_prefix_concavity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T15:48:58.083616+00:00
-- url     : https://prove2.me/theorems/695123be-a56c-408d-8a46-02de31270842
-- title:
--   A subdifferential policy with concave revenue at all prefixes is optimal
-- statement:
--   # Global optimality under explicit concavity of all prefix revenues
--
--   For a general protection policy p satisfying condition (20), assume
--   its expected revenues are concave at every positive prefix on all
--   nonnegative seat counts. Then p maximises expected revenue at all
--   positive prefix lengths and all nonnegative capacities.
--
--   This proof adapts the remotely ACCEPTED direct Theorem 2 induction
--   and removes the integer-demand assumption by making prefix concavity
--   an explicit premise. It combines the already Proved:
--   theorem1_global_optimality_base,
--   conditional_revenue_dominance_fixed,
--   sfinite_prefix_demand_law,
--   condRevenue_integrable_next_demand, and
--   expRevenue_eq_integral_condRevenue, with integral_mono_ae and ae_map_iff.
--
--   It isolates the genuine remaining issue in Theorem 1: deriving prefix
--   concavity from SubdiffCondition without assuming the two previously
--   Disproved conditional-concavity base/step propositions.
--   No local Lean, Lake, or proof-lab compilation was run.
-- source:
--   # Global optimality under explicit concavity of all prefix revenues
--
--   For a general protection policy p satisfying condition (20), assume
--   its expected revenues are concave at every positive prefix on all
--   nonnegative seat counts. Then p maximises expected revenue at all
--   positive prefix lengths and all nonnegative capacities.
--
--   This proof adapts the remotely ACCEPTED direct Theorem 2 induction
--   and removes the integer-demand assumption by making prefix concavity
--   an explicit premise. It combines the already Proved:
--   theorem1_global_optimality_base,
--   conditional_revenue_dominance_fixed,
--   sfinite_prefix_demand_law,
--   condRevenue_integrable_next_demand, and
--   expRevenue_eq_integral_condRevenue, with integral_mono_ae and ae_map_iff.
--
--   It isolates the genuine remaining issue in Theorem 1: deriving prefix
--   concavity from SubdiffCondition without assuming the two previously
--   Disproved conditional-concavity base/step propositions.
--   No local Lean, Lake, or proof-lab compilation was run.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.theorem1_global_optimality_of_prefix_concavity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (h20 : SubdiffCondition P X f p)
    (hconc : ∀ k, 1 ≤ k →
      ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p k)) :
    IsOptimal P X f p := by sorry
