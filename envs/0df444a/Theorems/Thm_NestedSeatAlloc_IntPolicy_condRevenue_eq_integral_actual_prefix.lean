-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_condRevenue_eq_integral_actual_prefix
-- name    : NestedSeatAlloc.IntPolicy.condRevenue_eq_integral_actual_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T14:17:21.356191+00:00
-- url     : https://prove2.me/theorems/28a191e6-7420-42f2-89d3-6c0419df1cc1
-- title:
--   Conditional expected revenue equals the integral over the actual higher-fare prefix law
-- statement:
--   # Concrete prefix-law identity for conditional nested expected revenue
--
--   The Proved condRevenue_eq_integral_prefix_law is stated with abstract
--   prefix U, demand reconstruction and two measurability/reconstruction
--   hypotheses. This theorem instantiates them with the ACTUAL demand
--   prefix U(ω)(i)=X i ω for i in Finset.Icc 1 k and with the existing
--   prefixRevenueRebuild k.
--
--   The Proved measurable_prefix_vector supplies Measurable U. The Proved
--   measurable_prefixRevenueRebuild and revenue_joint_measurable establish
--   joint measurability of the reconstructed revenue at fixed s, through
--   composition with a constant second coordinate. The separately
--   published revenue_frozen_prefix_rebuild supplies the equality between
--   the frozen demand path and the reconstructed path, using extensionality
--   of revenue on its finite prefix. Apply
--   condRevenue_eq_integral_prefix_law directly to conclude.
--
--   This equality identifies the inner integral obtained from factoring
--   the joint law of (X(k+1), U) with condRevenue as defined in the model.
--   The only remaining stochastic obligations are independence/product law
--   and justified product-measure integrability before using Fubini.
--
--   The proof is subject to the remote compiler; its import of
--   revenue_frozen_prefix_rebuild must be Proved before closure.
-- source:
--   # Concrete prefix-law identity for conditional nested expected revenue
--
--   The Proved condRevenue_eq_integral_prefix_law is stated with abstract
--   prefix U, demand reconstruction and two measurability/reconstruction
--   hypotheses. This theorem instantiates them with the ACTUAL demand
--   prefix U(ω)(i)=X i ω for i in Finset.Icc 1 k and with the existing
--   prefixRevenueRebuild k.
--
--   The Proved measurable_prefix_vector supplies Measurable U. The Proved
--   measurable_prefixRevenueRebuild and revenue_joint_measurable establish
--   joint measurability of the reconstructed revenue at fixed s, through
--   composition with a constant second coordinate. The separately
--   published revenue_frozen_prefix_rebuild supplies the equality between
--   the frozen demand path and the reconstructed path, using extensionality
--   of revenue on its finite prefix. Apply
--   condRevenue_eq_integral_prefix_law directly to conclude.
--
--   This equality identifies the inner integral obtained from factoring
--   the joint law of (X(k+1), U) with condRevenue as defined in the model.
--   The only remaining stochastic obligations are independence/product law
--   and justified product-measure integrability before using Fubini.
--
--   The proof is subject to the remote compiler; its import of
--   revenue_frozen_prefix_rebuild must be Proved before closure.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_prefixRevenueRebuild
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.condRevenue_eq_integral_actual_prefix {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (k : ℕ) (y s : ℝ) :
    (∫ u : (Finset.Icc 1 k → ℝ),
      revenue f p (prefixRevenueRebuild k (y, u)) (k + 1) s
        ∂(Measure.map
          (fun ω : Ω => fun i : (Finset.Icc 1 k) => X i.1 ω) P)) =
      condRevenue P X f p (k + 1) y s := by sorry
