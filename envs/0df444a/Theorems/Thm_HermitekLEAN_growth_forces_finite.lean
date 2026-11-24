-- Prove2me | Theorems.Thm_HermitekLEAN_growth_forces_finite
-- name    : HermitekLEAN.growth_forces_finite
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:14:19.934848+00:00
-- url     : https://prove2.me/theorems/9cf9fb5d-cd02-4dd9-8024-165a68ad5f74
-- title:
--   Hermitek LEAN: growth forces finite
-- statement:
--   The Hermitek LEAN construction uses the growth forces finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/ModulusRigidity.lean#L457-L569
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/ModulusRigidity.lean#L457-L569

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

theorem HermitekLEAN.growth_forces_finite :
    ∀ {k d : ℕ}
      (a : Fin (d + 1) → ℂ)
      (_hTop : topCoeff a ≠ 0)
      {G : ℂ → ℂ},
        G ∈ Hk k →
          (∀ z : ℂ, ‖G z‖ = ‖finiteHermiteSum k a z‖) →
            ∀ n : ℕ, d < n → hermiteCoeff k G n = 0 := by sorry
