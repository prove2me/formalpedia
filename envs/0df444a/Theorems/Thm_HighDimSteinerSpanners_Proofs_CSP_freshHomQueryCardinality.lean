-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_freshHomQueryCardinality
-- name    : HighDimSteinerSpanners.Proofs.CSP.freshHomQueryCardinality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:46.547801+00:00
-- url     : https://prove2.me/theorems/8e440be6-591b-4add-9cd0-b1a4ce6879a2
-- title:
--   CSP: fresh Hom Query Cardinality
-- statement:
--   The CSP construction uses the fresh Hom Query Cardinality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/CherryMoments.lean#L31-L109
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/CherryMoments.lean#L31-L109

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.GCongr
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessMoments
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_CherryMoments
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section

theorem HighDimSteinerSpanners.Proofs.CSP.freshHomQueryCardinality : ∀ {N q : ℕ} (z : Fin N → Fin q) (S_old : Finset (Fin N → Fin q))
    (T : Finset (Fin N)), (∀ v ∈ T, ∀ y ∈ S_old, z v ≠ y v) →
    T.card * (N - 1) - T.card.choose 2 ≤ (homQueries z \ S_old.biUnion homQueries).card := by sorry
