-- Prove2me | Theorems.Thm_MinBuying_exchangeable_construction_valid
-- name    : MinBuying.exchangeable_construction_valid
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T17:35:51.759116+00:00
-- url     : https://prove2.me/theorems/c679fa1d-383d-4045-a724-e9d4519a752e
-- title:
--   The explicit exchangeable-gap law is a finite supported probability law
-- statement:
--   For every natural number $n$, the explicitly defined exchangeableGapLaw is a probability measure, has nonnegative valuation coordinates almost surely, is invariant under every permutation of its coordinates, and is concentrated on a finite set of valuation vectors. Its mass consists of the stated geometric type mixture and the all-zero atom.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript. https://doi.org/10.2139/ssrn.5178133 . Theorem 3 construction, ec5–ec6, including its normalization and exchangeability statements.

import Definitions.Def_MinBuying_ExchangeableConstruction

open MeasureTheory Set MinBuying

namespace MinBuying

theorem exchangeable_construction_valid (n : ℕ) :
    ValidLaw (exchangeableGapLaw n) ∧ Exchangeable (exchangeableGapLaw n) ∧
    ∃ S : Finset (Valuations n), ∀ᵐ v ∂exchangeableGapLaw n, v ∈ S := by
  sorry

end MinBuying
