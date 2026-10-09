-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_integrable_product_prefix_revenue
-- name    : NestedSeatAlloc.IntPolicy.integrable_product_prefix_revenue
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T14:23:18.312516+00:00
-- url     : https://prove2.me/theorems/bc89a424-0ebb-4d63-93d6-31ad47e48cd8
-- title:
--   Reconstructed nested revenue is integrable under the product of the next demand and higher-fare prefix laws
-- statement:
--   # Product-law integrability for reconstructed airline-seat revenue
--
--   For any nonnegative seat count s and policy p satisfying IsProtectionPolicy, expected realised revenue through class k+1 is integrable by the already Proved revenue_integrable_of_seat_model.
--
--   Define U to be the measurable vector of demands indexed by Finset.Icc 1 k and Z=X(k+1). Define F(z,u)=revenue f p (prefixRevenueRebuild k (z,u)) (k+1) s.
--
--   The Proved measurable_prefix_vector and measurable_prefixRevenueRebuild, together with revenue_joint_measurable, give measurability of the joint variable (Z,U) and of F. The published revenue_actual_prefix_rebuild identity says F(Z ω,U ω) equals the actual realised revenue, so it is integrable on P.
--
--   The exact pinned Mathlib lemma integrable_map_measure transfers that integrability to the joint pushforward law of (Z,U). The published prefix_next_joint_product_law identifies this pushforward with the product of the next-class marginal and the finite-prefix marginal, giving the conclusion.
--
--   This discharges the integrability premise of the already Proved product_law_integral_nested_sfinite theorem when specialised to the seat model. Together with the conditional-prefix integral and the independent-demand factorisation, it supports expRevenue_eq_integral_condRevenue.
--
--   This is a separate draft pending acceptance of its imported named helpers; no local Lean was run.
-- source:
--   # Product-law integrability for reconstructed airline-seat revenue
--
--   For any nonnegative seat count s and policy p satisfying IsProtectionPolicy, expected realised revenue through class k+1 is integrable by the already Proved revenue_integrable_of_seat_model.
--
--   Define U to be the measurable vector of demands indexed by Finset.Icc 1 k and Z=X(k+1). Define F(z,u)=revenue f p (prefixRevenueRebuild k (z,u)) (k+1) s.
--
--   The Proved measurable_prefix_vector and measurable_prefixRevenueRebuild, together with revenue_joint_measurable, give measurability of the joint variable (Z,U) and of F. The published revenue_actual_prefix_rebuild identity says F(Z ω,U ω) equals the actual realised revenue, so it is integrable on P.
--
--   The exact pinned Mathlib lemma integrable_map_measure transfers that integrability to the joint pushforward law of (Z,U). The published prefix_next_joint_product_law identifies this pushforward with the product of the next-class marginal and the finite-prefix marginal, giving the conclusion.
--
--   This discharges the integrability premise of the already Proved product_law_integral_nested_sfinite theorem when specialised to the seat model. Together with the conditional-prefix integral and the independent-demand factorisation, it supports expRevenue_eq_integral_condRevenue.
--
--   This is a separate draft pending acceptance of its imported named helpers; no local Lean was run.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_prefixRevenueRebuild
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.integrable_product_prefix_revenue {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (k : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    Integrable
      (fun z : ℝ × (Finset.Icc 1 k → ℝ) =>
        revenue f p (prefixRevenueRebuild k z) (k + 1) s)
      ((Measure.map (X (k + 1)) P).prod
        (Measure.map
          (fun ω : Ω => fun i : (Finset.Icc 1 k) => X i.1 ω) P)) := by sorry
