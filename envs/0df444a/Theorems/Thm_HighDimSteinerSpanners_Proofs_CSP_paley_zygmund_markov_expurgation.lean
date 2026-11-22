-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_paley_zygmund_markov_expurgation
-- name    : HighDimSteinerSpanners.Proofs.CSP.paley_zygmund_markov_expurgation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:49:30.444693+00:00
-- url     : https://prove2.me/theorems/a624d439-5050-40a6-a037-eccabc8d7f9c
-- title:
--   CSP: paley zygmund markov expurgation
-- statement:
--   The CSP construction uses the paley zygmund markov expurgation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Expurgation.lean#L329-L519
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Expurgation.lean#L329-L519

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Prod
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Bernoulli
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Expurgation
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
open Classical

theorem HighDimSteinerSpanners.Proofs.CSP.paley_zygmund_markov_expurgation {Ω V : Type} [Fintype Ω]
    (W : Ω → ℝ) (hW_nn : ∀ ω : Ω, 0 ≤ W ω) (hW_sum : ∑ ω : Ω, W ω = 1)
    (Rel : V → V → Prop) [DecidableRel Rel] (hRel_symm : Std.Symm Rel)
    (P_raw B_bad : Ω → Finset V)
    (n_0 D_star γ δ_bad : ℝ)
    (hn0 : 0 < n_0) (hD : 0 < D_star) (hγ : 1 ≤ γ) (hδ : 0 < δ_bad)
    (h_margin : 72 * 144 * γ ^ 3 * δ_bad ≤ 1 / 256)
    (hM1 : ∑ ω : Ω, W ω * ((P_raw ω).card : ℝ) ≤ n_0)
    (hE1 : n_0 * D_star ≤ ∑ ω : Ω, W ω *
      (((P_raw ω ×ˢ P_raw ω).filter (fun xy => Rel xy.1 xy.2)).card : ℝ))
    (hE2 : ∑ ω : Ω, W ω *
      ((((P_raw ω ×ˢ P_raw ω).filter (fun xy => Rel xy.1 xy.2)).card : ℝ) ^ 2) ≤
        3 * γ * (n_0 * D_star) ^ 2)
    (hW2 : ∑ ω : Ω, W ω *
      (∑ x ∈ P_raw ω, (((P_raw ω).filter (fun y => Rel x y)).card : ℝ) ^ 2) ≤
        2 * γ * n_0 * D_star ^ 2)
    (hBad : ∑ ω : Ω, W ω * ((B_bad ω).card : ℝ) ≤ δ_bad * n_0) :
    ∃ ω₀ : Ω,
      (1 / 1024 : ℝ) * γ⁻¹ ^ 2 * n_0 ≤ ((P_raw ω₀ \ B_bad ω₀).card : ℝ) ∧
      ((P_raw ω₀ \ B_bad ω₀).card : ℝ) ≤ 72 * γ * n_0 ∧
      (D_star / γ) * ((P_raw ω₀ \ B_bad ω₀).card : ℝ) ≤
        192 * ((((P_raw ω₀ \ B_bad ω₀) ×ˢ (P_raw ω₀ \ B_bad ω₀)).filter
          (fun xy => Rel xy.1 xy.2)).card : ℝ) := by sorry
