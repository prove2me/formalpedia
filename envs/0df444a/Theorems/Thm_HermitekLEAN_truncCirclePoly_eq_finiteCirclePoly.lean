-- Prove2me | Theorems.Thm_HermitekLEAN_truncCirclePoly_eq_finiteCirclePoly
-- name    : HermitekLEAN.truncCirclePoly_eq_finiteCirclePoly
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:30:11.39581+00:00
-- url     : https://prove2.me/theorems/197bc0c5-ac0c-4d13-bfc5-0b69ff7adbb8
-- title:
--   Hermitek LEAN: trunc Circle Poly eq finite Circle Poly
-- statement:
--   The truncated circle polynomial is the finite circle polynomial of the truncated vector.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1863-L1868
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1863-L1868

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

theorem HermitekLEAN.truncCirclePoly_eq_finiteCirclePoly :
    ∀ {k J : ℕ} {G : ℂ → ℂ} {r : ℝ},
      truncCirclePoly k r J G =
        finiteCirclePoly k r (fun n : Fin (J + 1) => hermiteCoeff k G n.1) := by sorry
