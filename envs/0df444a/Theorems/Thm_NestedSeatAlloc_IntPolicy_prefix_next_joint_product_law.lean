-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_prefix_next_joint_product_law
-- name    : NestedSeatAlloc.IntPolicy.prefix_next_joint_product_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T14:19:25.678109+00:00
-- url     : https://prove2.me/theorems/0b49d536-d3e2-4450-abd0-3e8bc60e407c
-- title:
--   Independent prefix and next demand have the product of their marginal laws
-- statement:
--   # The joint law of next demand and prefix is a product
--
--   The Proved measurable_prefix_vector gives measurability of U(ω), the
--   vector X(1),...,X(k). The published indep_prefix_next_demand lemma
--   gives IndepFun U (X(k+1)) P. By symmetry this is IndepFun Z U P,
--   where Z=X(k+1). By hM.isProb, P is a finite probability measure.
--   The exact pinned Mathlib theorem
--   indepFun_iff_map_prod_eq_prod_map_map then identifies the
--   push-forward joint law of (Z,U) as (P.map Z).prod (P.map U).
--
--   This is the hjoint premise of the proved
--   product_law_integral_nested_sfinite theorem. It removes the key
--   probabilistic step from the final revenue-specific integral identity.
--   The remaining steps are to verify product integrability of the
--   reconstructed revenue and to identify its inner integral with
--   condRevenue_eq_integral_actual_prefix.
--
--   The theorem is a source-faithful proof obligation. No local Lean was
--   run; remote acceptance is necessary.
-- source:
--   # The joint law of next demand and prefix is a product
--
--   The Proved measurable_prefix_vector gives measurability of U(ω), the
--   vector X(1),...,X(k). The published indep_prefix_next_demand lemma
--   gives IndepFun U (X(k+1)) P. By symmetry this is IndepFun Z U P,
--   where Z=X(k+1). By hM.isProb, P is a finite probability measure.
--   The exact pinned Mathlib theorem
--   indepFun_iff_map_prod_eq_prod_map_map then identifies the
--   push-forward joint law of (Z,U) as (P.map Z).prod (P.map U).
--
--   This is the hjoint premise of the proved
--   product_law_integral_nested_sfinite theorem. It removes the key
--   probabilistic step from the final revenue-specific integral identity.
--   The remaining steps are to verify product integrability of the
--   reconstructed revenue and to identify its inner integral with
--   condRevenue_eq_integral_actual_prefix.
--
--   The theorem is a source-faithful proof obligation. No local Lean was
--   run; remote acceptance is necessary.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.prefix_next_joint_product_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f) (k : ℕ) :
    Measure.map
      (fun ω : Ω => (X (k + 1) ω,
        fun i : (Finset.Icc 1 k) => X i.1 ω)) P =
    (Measure.map (X (k + 1)) P).prod
      (Measure.map
        (fun ω : Ω => fun i : (Finset.Icc 1 k) => X i.1 ω) P) := by sorry
