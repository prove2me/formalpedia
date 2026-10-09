-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_condRevenue_integrable_next_demand
-- name    : NestedSeatAlloc.IntPolicy.condRevenue_integrable_next_demand
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T15:00:49.51985+00:00
-- url     : https://prove2.me/theorems/d96b6698-3e73-4257-82f3-f9b430494786
-- title:
--   Conditional nested expected revenue is integrable under the marginal next-demand law
-- statement:
--   # Conditional expected revenue is marginally integrable
--
--   For nonnegative capacity s and an admissible protection policy p,
--   the proven product-law integrability theorem establishes integrability
--   of F(y,u)=revenue f p (prefixRevenueRebuild k (y,u)) (k+1) s
--   under the product of the marginal next-demand law and prefix law.
--
--   Supply the explicit SFinite instance for the prefix law, which is the
--   hypothesis of Mathlib's Integrable.integral_prod_left. That theorem
--   yields integrability in y of the inner u-integral. The proved
--   condRevenue_eq_integral_actual_prefix identifies the inner integral
--   for each y with the model's condRevenue P X f p (k+1) y s.
--   Extensional replacement completes the argument.
--
--   This lemma explicitly exposes the marginal s-finiteness premise;
--   in the actual airline model it follows from hM.isProb and
--   measurable_prefix_vector, because the push-forward of a probability
--   measure is a probability measure. Avoid silently assuming that property
--   for a generic non-finite measure.
--
--   The result supports integral_mono_ae in the global optimality
--   induction, and does not claim the main theorem until the independent
--   remote verifier has accepted this proof.
-- source:
--   # Conditional expected revenue is marginally integrable
--
--   For nonnegative capacity s and an admissible protection policy p,
--   the proven product-law integrability theorem establishes integrability
--   of F(y,u)=revenue f p (prefixRevenueRebuild k (y,u)) (k+1) s
--   under the product of the marginal next-demand law and prefix law.
--
--   Supply the explicit SFinite instance for the prefix law, which is the
--   hypothesis of Mathlib's Integrable.integral_prod_left. That theorem
--   yields integrability in y of the inner u-integral. The proved
--   condRevenue_eq_integral_actual_prefix identifies the inner integral
--   for each y with the model's condRevenue P X f p (k+1) y s.
--   Extensional replacement completes the argument.
--
--   This lemma explicitly exposes the marginal s-finiteness premise;
--   in the actual airline model it follows from hM.isProb and
--   measurable_prefix_vector, because the push-forward of a probability
--   measure is a probability measure. Avoid silently assuming that property
--   for a generic non-finite measure.
--
--   The result supports integral_mono_ae in the global optimality
--   induction, and does not claim the main theorem until the independent
--   remote verifier has accepted this proof.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.condRevenue_integrable_next_demand {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (k : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hsU : SFinite (Measure.map
      (fun ω : Ω => fun i : (Finset.Icc 1 k) => X i.1 ω) P)) :
    Integrable (fun y => condRevenue P X f p (k + 1) y s)
      (Measure.map (X (k + 1)) P) := by sorry
