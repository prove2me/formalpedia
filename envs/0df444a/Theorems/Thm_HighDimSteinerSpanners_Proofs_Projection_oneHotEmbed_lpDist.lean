-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_Projection_oneHotEmbed_lpDist
-- name    : HighDimSteinerSpanners.Proofs.Projection.oneHotEmbed_lpDist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:47.418797+00:00
-- url     : https://prove2.me/theorems/7c5b501d-0ece-4a23-8543-db6db8da72b4
-- title:
--   Projection: one Hot Embed lp Dist
-- statement:
--   Compatibility name for the shared one-hot embedding distance formula.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Projection.lean#L332-L334
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Projection.lean#L332-L334

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
public import Definitions.Def_LeanPool_SteinerSpanners_Projection
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Geometry_oneHotEmbed_lpDist

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Projection

theorem HighDimSteinerSpanners.Proofs.Projection.oneHotEmbed_lpDist {N q : ℕ} (p : ℝ) (hp : 1 ≤ p) : ∀ x y : Fin N → Fin q,
    lpDist p (oneHotEmbed x) (oneHotEmbed y) = (2 * (hammingDist x y : ℝ)) ^ (1 / p) := by sorry
