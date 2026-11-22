-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_candMWit_proj
-- name    : HighDimSteinerSpanners.Proofs.CSP.candMWit_proj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:49.080993+00:00
-- url     : https://prove2.me/theorems/75a8f06e-215b-4ad6-9800-657a178a0cf1
-- title:
--   CSP: cand MWit proj
-- statement:
--   The CSP construction uses the cand MWit proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessProjection.lean#L138-L343
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessProjection.lean#L138-L343

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

theorem HighDimSteinerSpanners.Proofs.CSP.candMWit_proj {N q : ℕ} (C₁ r_star m : ℕ)
    (a b : Fin N → Fin q) (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q)
    (ω : cspIota N q → Bool) (hω_keep : ω (Sum.inr x) = true)
    (hx_wit : x ∈ bicliqueWitnessList (symROf ω) C₁ r_star a b) :
    ∃ w ∈ candMWit C₁ r_star a b m z_prev x,
      ∀ i ∈ candQCand C₁ a b m z_prev x w, ω i = true := by sorry
