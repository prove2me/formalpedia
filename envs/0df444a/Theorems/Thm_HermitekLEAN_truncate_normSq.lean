-- Prove2me | Theorems.Thm_HermitekLEAN_truncate_normSq
-- name    : HermitekLEAN.truncate_normSq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:00:28.21081+00:00
-- url     : https://prove2.me/theorems/164ab480-793c-448c-a00d-a16eb3e0630a
-- title:
--   Hermitek LEAN: truncate norm Sq
-- statement:
--   Exact finite Parseval identity for Hermite truncations.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1951-L1957
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1951-L1957

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

theorem HermitekLEAN.truncate_normSq :
    ∀ (k J : ℕ) (G : ℂ → ℂ),
      weightedNormSq (truncate k J G) =
        ∑ n : Fin (J + 1), ‖hermiteCoeff k G n.1‖ ^ 2 := by sorry
