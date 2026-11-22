-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_Glue_lem_5_1_proof
-- name    : HighDimSteinerSpanners.Proofs.Glue.lem_5_1_proof
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:00.565216+00:00
-- url     : https://prove2.me/theorems/39e80117-159f-4364-9eaf-0cf4d69730f7
-- title:
--   Glue: lem 5 1 proof
-- statement:
--   Zero-`sorry` proof of Lemma 5.1 (`lem_5_1_interval_crossing`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Glue.lean#L42-L121
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Glue.lean#L42-L121

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

theorem HighDimSteinerSpanners.Proofs.Glue.lem_5_1_proof :
    ∀ (α β : ℤ), 1 ≤ α → α ≤ β →
      ∀ (L R : ℤ → ℤ),
        (∀ s : ℤ, α ≤ s → s ≤ β →
          α - 1 ≤ L s ∧ L s ≤ s - 1 ∧ s ≤ R s ∧ R s ≤ β ∧ (L s, R s) ≠ (α - 1, β)) →
        ∃ s t : ℤ,
          α ≤ s ∧ s < t ∧ t ≤ β ∧
          L s < L t ∧ L t ≤ s ∧ t ≤ R s + 1 ∧ R s + 1 ≤ R t := by sorry
