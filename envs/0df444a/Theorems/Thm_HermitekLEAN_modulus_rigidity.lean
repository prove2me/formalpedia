-- Prove2me | Theorems.Thm_HermitekLEAN_modulus_rigidity
-- name    : HermitekLEAN.modulus_rigidity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:45:46.803904+00:00
-- url     : https://prove2.me/theorems/3ed1db05-47f0-4e28-9a40-98f6707057b9
-- title:
--   Hermitek LEAN: modulus rigidity
-- statement:
--   Full modulus rigidity inside `H_k`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/ModulusRigidity.lean#L793-L820
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/ModulusRigidity.lean#L793-L820

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

theorem HermitekLEAN.modulus_rigidity :
    ∀ {k d : ℕ}
      (a : Fin (d + 1) → ℂ)
      (_hTop : topCoeff a ≠ 0)
      {G : ℂ → ℂ},
        G ∈ Hk k →
          (∀ z : ℂ, ‖G z‖ = ‖finiteHermiteSum k a z‖) →
            ∃ w : ℂ, ‖w‖ = 1 ∧ G = w • finiteHermiteSum k a := by sorry
