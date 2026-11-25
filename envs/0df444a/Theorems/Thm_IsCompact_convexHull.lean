-- Prove2me | Theorems.Thm_IsCompact_convexHull
-- name    : IsCompact.convexHull
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:18:27.628166+00:00
-- url     : https://prove2.me/theorems/dd1ef356-b3fd-431f-b8a1-eb7951984cf4
-- title:
--   Is Compact: convex Hull
-- statement:
--   **The convex hull of a compact set is compact**, in a finite-dimensional real normed
--   space. Mathlib has the finite-set case (`Set.Finite.isCompact_convexHull`) and
--   `TotallyBounded.convexHull`, which gives total boundedness of the hull and so
--   compactness only of its *closure*; the point here is that in finite dimension the
--   hull is already closed.
--
--   By Carathéodory's theorem every point of the hull is a convex combination of at most
--   `finrank ℝ E + 1` affinely independent points of `s`, so the hull is the image of the
--   compact set `{weights} × s^(finrank+1)` under the continuous map `(w, z) ↦ ∑ᵢ wᵢ • zᵢ`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/CompactConvexHull.lean#L58-L128
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/CompactConvexHull.lean#L58-L128

module
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Definitions.Def_BasicResults_CompactConvexHull
set_option autoImplicit true
@[expose] public section
public section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCompact.convexHull {s : Set E} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by sorry
