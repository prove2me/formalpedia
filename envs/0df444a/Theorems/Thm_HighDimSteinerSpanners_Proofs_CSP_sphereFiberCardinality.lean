-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_sphereFiberCardinality
-- name    : HighDimSteinerSpanners.Proofs.CSP.sphereFiberCardinality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:49.711485+00:00
-- url     : https://prove2.me/theorems/047eb0ea-a187-4e4b-960b-ddf9cdefd3cd
-- title:
--   CSP: sphere Fiber Cardinality
-- statement:
--   The CSP construction uses the sphere Fiber Cardinality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/CherryMoments.lean#L111-L170
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/CherryMoments.lean#L111-L170

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

theorem HighDimSteinerSpanners.Proofs.CSP.sphereFiberCardinality : ∀ {N q : ℕ} (x : Fin N → Fin q) (U : Finset (Fin N)) (s : ℕ),
    (Finset.univ.filter (fun g : Fin N → Fin q => (∀ v ∉ U, g v = x v) ∧ dHam x g = s)).card =
      U.card.choose s * (q - 1) ^ s := by sorry
