-- Prove2me | Theorems.Thm_HermitekLEAN_finiteHermiteSum_normSq
-- name    : HermitekLEAN.finiteHermiteSum_normSq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:16.372028+00:00
-- url     : https://prove2.me/theorems/77a251c4-7ada-4794-99af-d24c3ddf3245
-- title:
--   Hermitek LEAN: finite Hermite Sum norm Sq
-- statement:
--   The weighted norm square of a finite Hermite sum is the coefficient `ℓ²` norm square.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1678-L1683
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1678-L1683

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN

theorem HermitekLEAN.finiteHermiteSum_normSq :
    ∀ {k D : ℕ} (a : Fin D → ℂ),
      weightedNormSq (finiteHermiteSum k a) = ∑ n : Fin D, ‖a n‖ ^ 2 := by sorry
