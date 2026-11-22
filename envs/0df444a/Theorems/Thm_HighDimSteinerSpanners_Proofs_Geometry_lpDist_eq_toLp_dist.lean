-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_Geometry_lpDist_eq_toLp_dist
-- name    : HighDimSteinerSpanners.Proofs.Geometry.lpDist_eq_toLp_dist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:44.222005+00:00
-- url     : https://prove2.me/theorems/2bbc6c88-2adf-4d81-a899-4657d26f23ff
-- title:
--   Geometry: lp Dist eq to Lp dist
-- statement:
--   The explicit finite-coordinate distance agrees with Mathlib's `WithLp` metric.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Geometry.lean#L32-L39
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Geometry.lean#L32-L39

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Geometry
noncomputable section

theorem HighDimSteinerSpanners.Proofs.Geometry.lpDist_eq_toLp_dist (p : ℝ) (hp : 1 ≤ p) {d : ℕ} (x y : Fin d → ℝ) :
    lpDist p x y =
      dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y) := by sorry
