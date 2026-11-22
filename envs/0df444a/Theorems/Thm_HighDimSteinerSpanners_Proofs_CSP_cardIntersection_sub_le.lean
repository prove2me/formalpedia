-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_cardIntersection_sub_le
-- name    : HighDimSteinerSpanners.Proofs.CSP.cardIntersection_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:48.226002+00:00
-- url     : https://prove2.me/theorems/739cb5f4-ffdd-489b-a866-150616518e7a
-- title:
--   CSP: card Intersection sub le
-- statement:
--   Convert a real cardinality deficit into a rounded bound for an intersection.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessProjection.lean#L130-L136
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessProjection.lean#L130-L136

module
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessCardinality
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessProjection
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section

theorem HighDimSteinerSpanners.Proofs.CSP.cardIntersection_sub_le {α : Type*} [DecidableEq α] (M A B : Finset α) (r : ℕ)
    (h : (A.card : ℝ) - 11 / 40 * r ≤ B.card) :
    (M ∩ A).card - (11 * r) / 40 ≤ B.card := by sorry
