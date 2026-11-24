-- Prove2me | Theorems.Thm_HermitekLEAN_leading_term_extraction
-- name    : HermitekLEAN.leading_term_extraction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:45:16.301797+00:00
-- url     : https://prove2.me/theorems/d3537947-99f6-4883-acbb-c66b9dcd5f9b
-- title:
--   Hermitek LEAN: leading term extraction
-- statement:
--   If a unique top-order term survives asymptotically, its coefficient must vanish.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/ModulusRigidity.lean#L32-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/ModulusRigidity.lean#L32-L63

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ModulusRigidity
set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped Topology
noncomputable section
open HermitekLEAN

theorem HermitekLEAN.leading_term_extraction :
    ∀ {N : ℕ} {α : ℂ} {q : ℝ → ℂ},
      (∀ ε : ℝ, 0 < ε → ∃ R0 : ℝ, ∀ r ≥ R0, ‖q r / (r ^ N : ℂ)‖ ≤ ε) →
        (∃ R0 : ℝ, ∀ r ≥ R0, α * (r ^ N : ℂ) + q r = 0) →
          α = 0 := by sorry
