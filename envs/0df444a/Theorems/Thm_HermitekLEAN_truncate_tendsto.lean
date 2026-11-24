-- Prove2me | Theorems.Thm_HermitekLEAN_truncate_tendsto
-- name    : HermitekLEAN.truncate_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:31:13.378891+00:00
-- url     : https://prove2.me/theorems/b8e6bc23-6fd3-4c95-856e-417956e490ff
-- title:
--   Hermitek LEAN: truncate tendsto
-- statement:
--   Truncations converge to `G` in the weighted norm.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L3499-L3585
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L3499-L3585

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

theorem HermitekLEAN.truncate_tendsto :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        ∀ ε : ℝ,
          0 < ε →
            ∃ J0 : ℕ, ∀ J ≥ J0, weightedNorm (truncate k J G - G) ≤ ε := by sorry
