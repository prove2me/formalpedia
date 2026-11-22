-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_Projection_oneHotEmbed_injective
-- name    : HighDimSteinerSpanners.Proofs.Projection.oneHotEmbed_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:08.405009+00:00
-- url     : https://prove2.me/theorems/dce826ba-76b3-44ea-a7a8-9fff3c859b66
-- title:
--   Projection: one Hot Embed injective
-- statement:
--   The Projection construction uses the one Hot Embed injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Projection.lean#L336-L345
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Projection.lean#L336-L345

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
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Projection

theorem HighDimSteinerSpanners.Proofs.Projection.oneHotEmbed_injective {N q : ℕ} : Function.Injective (@oneHotEmbed N q) := by sorry
