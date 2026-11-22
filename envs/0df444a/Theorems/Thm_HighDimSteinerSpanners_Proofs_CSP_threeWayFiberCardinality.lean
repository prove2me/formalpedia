-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_threeWayFiberCardinality
-- name    : HighDimSteinerSpanners.Proofs.CSP.threeWayFiberCardinality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:43.598146+00:00
-- url     : https://prove2.me/theorems/193a156c-51ee-4d46-9618-6b544da9ad4d
-- title:
--   CSP: three Way Fiber Cardinality
-- statement:
--   The CSP construction uses the three Way Fiber Cardinality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/CherryMoments.lean#L172-L277
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/CherryMoments.lean#L172-L277

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

theorem HighDimSteinerSpanners.Proofs.CSP.threeWayFiberCardinality : ∀ {N q : ℕ} (x u : Fin N → Fin q) (d₃ w : ℕ),
    (Finset.univ.filter (fun z : Fin N → Fin q =>
      (threeWayDisagree x u z).card = d₃ ∧ (disagreeSet x z \ disagreeSet x u).card = w)).card ≤
      2 ^ (2 * dHam x u) * (q - 1) ^ d₃ * (N.choose w * (q - 1) ^ w) := by sorry
