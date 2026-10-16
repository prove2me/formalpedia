-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_finset_prod_series
-- name    : OAI.PiExponent.FormalInterpolation.hasWeightedSupport_finset_prod_series
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T06:14:30.603035+00:00
-- url     : https://prove2.me/theorems/78f4f200-bfe7-481d-9363-71eff5df5873
-- title:
--   Weighted support of finite products over finite sets
-- statement:
--   For any finite index set, if every power series in the family has weighted support at least R, then their product has weighted support at least the cardinality of the index set times R.
-- source:
--   Adapted from formalJet_mem_weighted_of_mem_pow in CompactJetPolynomial.lean, cited by the parent target.

import Definitions.Def_OAI_PiExponent_WeightedSupport

open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.hasWeightedSupport_finset_prod_series {m : ℕ} (v : Fin (m + 1) → ℝ) (R : ℝ) {ι : Type} [DecidableEq ι] (t : Finset ι) (f : ι → MvPowerSeries (Fin (m + 1)) ℂ) (hf : ∀ i ∈ t, hasWeightedSupport v R (f i)) : hasWeightedSupport v ((t.card : ℝ) * R) (t.prod f) := by sorry
