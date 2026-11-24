-- Prove2me | Theorems.Thm_HermitekLEAN_truncate_locally_uniform
-- name    : HermitekLEAN.truncate_locally_uniform
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:11:54.085935+00:00
-- url     : https://prove2.me/theorems/157dab3e-a2d2-46b2-a235-5a5b8202b88a
-- title:
--   Hermitek LEAN: truncate locally uniform
-- statement:
--   Truncations converge locally uniformly on bounded sets.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L3588-L3729
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L3588-L3729

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

theorem HermitekLEAN.truncate_locally_uniform :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        ∀ R ε : ℝ,
          0 < R →
            0 < ε →
              ∃ J0 : ℕ,
                ∀ J ≥ J0,
                  ∀ z : ℂ, ‖z‖ ≤ R → ‖truncate k J G z - G z‖ ≤ ε := by sorry
