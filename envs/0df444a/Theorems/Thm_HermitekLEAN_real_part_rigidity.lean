-- Prove2me | Theorems.Thm_HermitekLEAN_real_part_rigidity
-- name    : HermitekLEAN.real_part_rigidity
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:45:46.838233+00:00
-- url     : https://prove2.me/theorems/db443976-eb6e-4b89-8fd1-da6dfa9d3117
-- title:
--   Hermitek LEAN: real part rigidity
-- statement:
--   The Hermitek LEAN construction uses the real part rigidity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/ModulusRigidity.lean#L1696-L1722
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/ModulusRigidity.lean#L1696-L1722

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

theorem HermitekLEAN.real_part_rigidity :
    ∀ {k d : ℕ}
      (a : Fin (d + 1) → ℂ)
      (_hTop : topCoeff a ≠ 0)
      {G : ℂ → ℂ},
        G ∈ Hk k →
          (∀ z : ℂ, Complex.re (G z * star (finiteHermiteSum k a z)) = 0) →
            ∃ c : ℝ, G = ((Complex.I * (c : ℂ)) • finiteHermiteSum k a) := by sorry
