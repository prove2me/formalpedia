-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_simplex_cofinal_cardinality_gap
-- name    : OAI.PiExponent.FormalInterpolation.weighted_simplex_cofinal_cardinality_gap
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T13:38:35.854192+00:00
-- url     : https://prove2.me/theorems/25eb42f4-b97e-4ebf-aa3c-2db17c8a713a
-- title:
--   Cofinal cardinality gap for weighted lattice simplices
-- statement:
--   For positive rational weights in positive dimension and a positive real dilation, the strict volume inequality gives cofinally many positive natural heights where the closed degree simplex has more lattice points than K copies of the strictly bounded jet simplex. Clear denominators, split exponent vectors into finitely many residue classes, and apply stars-and-bars to obtain the leading cardinality terms and a lower-order error.

import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.weighted_simplex_cofinal_cardinality_gap
    {d K : Nat} (w v : Fin d → Rat) (alpha : Real)
    (hd : 0 < d) (halpha : 0 < alpha)
    (hw : ∀ i, 0 < (w i : Real)) (hv : ∀ i, 0 < (v i : Real))
    (hvolume :
      (K : Real) * alpha ^ d * (∏ i, (w i : Real)) /
        (∏ i, (v i : Real)) < 1) :
    ∀ N₀ : Nat, ∃ N : Nat, N₀ ≤ N ∧ 0 < N ∧
      ∃ S T : Finset (Fin d →₀ Nat),
        (∀ a, a ∈ S ↔ (∑ i, (w i : Real) * (a i : Real)) ≤ (N : Real)) ∧
        (∀ a, a ∈ T ↔ (∑ i, (v i : Real) * (a i : Real)) < alpha * (N : Real)) ∧
        K * T.card < S.card := by sorry
