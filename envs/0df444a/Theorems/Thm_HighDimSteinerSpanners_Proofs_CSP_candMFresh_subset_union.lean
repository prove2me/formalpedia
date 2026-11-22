-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_candMFresh_subset_union
-- name    : HighDimSteinerSpanners.Proofs.CSP.candMFresh_subset_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:18.911796+00:00
-- url     : https://prove2.me/theorems/06b4d357-7934-4e28-bc2c-09e7007ba15d
-- title:
--   CSP: cand MFresh subset union
-- statement:
--   The CSP construction uses the cand MFresh subset union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessCardinality.lean#L30-L37
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessCardinality.lean#L30-L37

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_CalibrationBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessCardinality
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section

theorem HighDimSteinerSpanners.Proofs.CSP.candMFresh_subset_union {N q : ℕ} (a b : Fin N → Fin q)
    (m : ℕ) (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q) :
    candMFresh a b m z_prev x ⊆ disagreeSet x a ∪ disagreeSet x b := by sorry
