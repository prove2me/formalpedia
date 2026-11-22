-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_Geometry_oneHotEmbed_lpDist
-- name    : HighDimSteinerSpanners.Proofs.Geometry.oneHotEmbed_lpDist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:42.760798+00:00
-- url     : https://prove2.me/theorems/8b4090bc-55da-457a-a862-739648b5bbe3
-- title:
--   Geometry: one Hot Embed lp Dist
-- statement:
--   One-hot embedding turns Hamming distance into the corresponding scaled `ell-p` distance.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Geometry.lean#L42-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Geometry.lean#L42-L71

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

theorem HighDimSteinerSpanners.Proofs.Geometry.oneHotEmbed_lpDist {N q : ℕ} (p : ℝ) (hp : 1 ≤ p) : ∀ x y : Fin N → Fin q,
    lpDist p (oneHotEmbed x) (oneHotEmbed y) = (2 * (hammingDist x y : ℝ)) ^ (1 / p) := by sorry
