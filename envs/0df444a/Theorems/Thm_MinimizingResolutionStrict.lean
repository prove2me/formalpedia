-- Prove2me | Theorems.Thm_MinimizingResolutionStrict
-- name    : MinimizingResolutionStrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:59:58.012061+00:00
-- url     : https://prove2.me/theorems/27c7c452-41d8-49ec-8b04-6186f4d58b43
-- title:
--   Minimizing Resolution Strict: Minimizing Resolution Strict
-- statement:
--   Any resolution of `γ` into geodesic edges whose count of small (length `< δ`) edges equals
--   `smallPieceCount γ δ` is strictly monotone on its index range: a minimizing resolution carries no
--   degenerate (repeated-breakpoint) edges.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/MinimizingResolutionStrict.lean#L9-L177
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/MinimizingResolutionStrict.lean#L9-L177

import Definitions.Def_Tablet_smallPieceCount
import Definitions.Def_Tablet_MinimizingResolutionStrict
set_option autoImplicit false
open Set

theorem MinimizingResolutionStrict {E : Type*} [MetricSpace E] (γ : Curve E) (δ : ℝ) (hδ : 0 < δ)
    (k : ℕ) (s : ℕ → ℝ) (hres : IsGeodesicResolution γ k s)
    (hmin : ((Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < δ)).card
      = smallPieceCount γ δ) :
    StrictMonoOn s (Set.Icc 0 k) := by sorry
