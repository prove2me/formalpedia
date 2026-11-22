-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_bernoulli_cylinder
-- name    : HighDimSteinerSpanners.Proofs.CSP.bernoulli_cylinder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:49:03.408064+00:00
-- url     : https://prove2.me/theorems/fa75b711-1254-4608-b498-378c0d997792
-- title:
--   CSP: bernoulli cylinder
-- statement:
--   The CSP construction uses the bernoulli cylinder property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Bernoulli.lean#L36-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Bernoulli.lean#L36-L71

module
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessProjection
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Bernoulli
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section

theorem HighDimSteinerSpanners.Proofs.CSP.bernoulli_cylinder {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) : ∀ S : Finset ι,
    ∑ ω : ι → Bool, (if ∀ i ∈ S, ω i = true then bernWeight p ω else 0) = ∏ i ∈ S, p i := by sorry
