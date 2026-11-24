-- Prove2me | Theorems.Thm_HermitekLEAN_phi_explicit
-- name    : HermitekLEAN.phi_explicit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:59:59.342333+00:00
-- url     : https://prove2.me/theorems/989571f8-2ed0-476d-bd0a-2f0f7768d0c2
-- title:
--   Hermitek LEAN: phi explicit
-- statement:
--   Explicit finite expansion for the true Hermite basis vector `Phi k n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L280-L289
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L280-L289

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

theorem HermitekLEAN.phi_explicit :
    ∀ {k n : ℕ} {z : ℂ},
      Phi k n z =
        ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ) *
          Finset.sum (Finset.range (min k n + 1)) (fun j =>
            ((-1 : ℂ) ^ j) * (Nat.choose k j : ℂ) *
              ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ)) *
              z ^ (n - j) * (star z) ^ (k - j)) := by sorry
