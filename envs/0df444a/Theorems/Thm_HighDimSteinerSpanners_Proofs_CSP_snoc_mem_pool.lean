-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_snoc_mem_pool
-- name    : HighDimSteinerSpanners.Proofs.CSP.snoc_mem_pool
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:49:14.88085+00:00
-- url     : https://prove2.me/theorems/b4b9bb62-1801-4d90-932c-8060876e32e3
-- title:
--   CSP: snoc mem pool
-- statement:
--   The CSP construction uses the snoc mem pool property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Bernoulli.lean#L95-L101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Bernoulli.lean#L95-L101

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

theorem HighDimSteinerSpanners.Proofs.CSP.snoc_mem_pool {β : Type} (Pool : Finset β) : ∀ (m : ℕ) (z_prev : Fin m → β),
    (∀ t : Fin m, z_prev t ∈ Pool) →
    ∀ b ∈ Pool, ∀ u : Fin (m + 1), (Fin.snoc z_prev b : Fin (m + 1) → β) u ∈ Pool := by sorry
