-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_incidentQueryCardinality
-- name    : HighDimSteinerSpanners.Proofs.CSP.incidentQueryCardinality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:30.932452+00:00
-- url     : https://prove2.me/theorems/939df8de-8399-4a1e-961c-a7887812e2f8
-- title:
--   CSP: incident Query Cardinality
-- statement:
--   The CSP construction uses the incident Query Cardinality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessMoments.lean#L30-L137
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessMoments.lean#L30-L137

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Calibration
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessMoments
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section

theorem HighDimSteinerSpanners.Proofs.CSP.incidentQueryCardinality : ∀ {N : ℕ} (S : Finset (Fin N)),
    2 * ((S.card : ℤ) * ((N - 1 : ℕ) : ℤ) - ((candA1 S).card : ℤ)) ≤ (S.card : ℤ) ^ 2 := by sorry
