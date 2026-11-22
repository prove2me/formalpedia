-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_cherryFiberCardinality
-- name    : HighDimSteinerSpanners.Proofs.CSP.cherryFiberCardinality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:50.113358+00:00
-- url     : https://prove2.me/theorems/74cf2d73-0162-4f5c-87ad-203de4027c2d
-- title:
--   CSP: cherry Fiber Cardinality
-- statement:
--   The CSP construction uses the cherry Fiber Cardinality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/CherryMoments.lean#L279-L383
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/CherryMoments.lean#L279-L383

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

theorem HighDimSteinerSpanners.Proofs.CSP.cherryFiberCardinality : ∀ {N q : ℕ} (C₁ r_star : ℕ), 3 ≤ C₁ →
    ∀ (x : Fin N → Fin q) (R_old : Finset (Fin N × Fin q)),
    R_old.card ≤ 21 * C₁ ^ 2 * r_star →
    ∀ (s : ℕ),
    ((Finset.univ.filter (fun y : Fin N → Fin q =>
      ((disagreeSet x y).filter (fun v => (v, y v) ∉ R_old)).card = s ∧
      dHam x y ≤ r_star)).card : ℝ) ≤
      ((r_star + 1 : ℕ) : ℝ) *
        (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
        ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s) := by sorry
