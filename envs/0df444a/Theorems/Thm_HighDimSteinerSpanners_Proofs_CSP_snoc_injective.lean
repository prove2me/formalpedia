-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_snoc_injective
-- name    : HighDimSteinerSpanners.Proofs.CSP.snoc_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:58.151556+00:00
-- url     : https://prove2.me/theorems/843e7abc-237f-433a-b0c0-bd1238a69556
-- title:
--   CSP: snoc injective
-- statement:
--   The CSP construction uses the snoc injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Bernoulli.lean#L73-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Bernoulli.lean#L73-L93

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

theorem HighDimSteinerSpanners.Proofs.CSP.snoc_injective {β : Type} [DecidableEq β] (Pool : Finset β) : ∀ (m : ℕ) (z_prev : Fin m → β),
    Function.Injective z_prev →
    ∀ b ∈ Pool \ Finset.univ.image z_prev,
    Function.Injective (Fin.snoc z_prev b) := by sorry
