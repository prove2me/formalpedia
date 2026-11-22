-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_Glue_lpDist_eq_toLp_dist_proof
-- name    : HighDimSteinerSpanners.Proofs.Glue.lpDist_eq_toLp_dist_proof
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:47:59.409965+00:00
-- url     : https://prove2.me/theorems/bfc7d433-c019-447d-84f1-8aa5a61638e6
-- title:
--   Glue: lp Dist eq to Lp dist proof
-- statement:
--   Zero-`sorry` proof of `lpDist_eq_toLp_dist`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Glue.lean#L34-L39
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Glue.lean#L34-L39

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
public import Definitions.Def_LeanPool_SteinerSpanners_Glue
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Glue

theorem HighDimSteinerSpanners.Proofs.Glue.lpDist_eq_toLp_dist_proof :
    ∀ (p : ℝ), 1 ≤ p →
      ∀ {d : ℕ} (x y : Fin d → ℝ),
        lpDist p x y =
          dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y) := by sorry
