-- Prove2me | Theorems.Thm_HermitekLEAN_qkn_structure
-- name    : HermitekLEAN.qkn_structure
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:29:49.019251+00:00
-- url     : https://prove2.me/theorems/703479f7-ada1-43eb-aa6c-27de76f1a320
-- title:
--   Hermitek LEAN: qkn structure
-- statement:
--   Backward-compatible alias for the explicit Laurent expansion of `qkn`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L390-L400
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L390-L400

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

theorem HermitekLEAN.qkn_structure :
    ∀ {k n : ℕ} {r : ℝ},
      0 < r →
        qkn k n r =
          (1 / Real.sqrt (Nat.factorial n : ℝ)) *
            Finset.sum (Finset.range (min k n + 1)) (fun j =>
              ((-1 : ℝ) ^ j) * (Nat.choose k j : ℝ) *
                ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
                r ^ ((n : ℤ) - 2 * (j : ℤ))) := by sorry
