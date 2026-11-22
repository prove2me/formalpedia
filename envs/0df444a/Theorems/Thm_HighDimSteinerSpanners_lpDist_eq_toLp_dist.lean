-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_lpDist_eq_toLp_dist
-- name    : HighDimSteinerSpanners.lpDist_eq_toLp_dist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:53:40.032257+00:00
-- url     : https://prove2.me/theorems/2c0399b1-dfc6-4798-828c-40e91b77e918
-- title:
--   High Dim Steiner Spanners: lp Dist eq to Lp dist
-- statement:
--   The High Dim Steiner Spanners construction uses the lp Dist eq to Lp dist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners.lean#L44-L49
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners.lean#L44-L49

module
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Glue
public import Definitions.Def_LeanPool_SteinerSpanners_Projection
public import Definitions.Def_LeanPool_SteinerSpanners_Combinatorics
public import Definitions.Def_LeanPool_SteinerSpanners_CSP
public import Definitions.Def_LeanPool_SteinerSpanners_Bucketing
public import Definitions.Def_LeanPool_SteinerSpanners_Hamming
public import Definitions.Def_LeanPool_SteinerSpanners_Dvoretzky
public import Definitions.Def_LeanPool_SteinerSpanners
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Geometry_lpDist_eq_toLp_dist

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners

theorem HighDimSteinerSpanners.lpDist_eq_toLp_dist :
    ∀ (p : ℝ), 1 ≤ p →
      ∀ {d : ℕ} (x y : Fin d → ℝ),
        lpDist p x y =
          dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y) := by sorry
