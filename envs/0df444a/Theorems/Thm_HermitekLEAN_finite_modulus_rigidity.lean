-- Prove2me | Theorems.Thm_HermitekLEAN_finite_modulus_rigidity
-- name    : HermitekLEAN.finite_modulus_rigidity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:14:22.372156+00:00
-- url     : https://prove2.me/theorems/f4b26ee0-b29c-4ee0-b1f3-7d8f59d14a7c
-- title:
--   Hermitek LEAN: finite modulus rigidity
-- statement:
--   Finite modulus rigidity up to a unimodular scalar.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/ModulusRigidity.lean#L732-L790
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/ModulusRigidity.lean#L732-L790

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

theorem HermitekLEAN.finite_modulus_rigidity :
    ∀ {k d : ℕ}
      (a b : Fin (d + 1) → ℂ)
      (_hTop : topCoeff a ≠ 0),
        (∀ z : ℂ, ‖finiteHermiteSum k b z‖ = ‖finiteHermiteSum k a z‖) →
          ∃ w : ℂ, ‖w‖ = 1 ∧ finiteHermiteSum k b = w • finiteHermiteSum k a := by sorry
