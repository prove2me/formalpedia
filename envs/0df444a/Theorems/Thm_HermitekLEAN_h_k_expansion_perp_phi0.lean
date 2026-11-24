-- Prove2me | Theorems.Thm_HermitekLEAN_h_k_expansion_perp_phi0
-- name    : HermitekLEAN.h_k_expansion_perp_phi0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:31:16.381663+00:00
-- url     : https://prove2.me/theorems/d673ef18-7c38-43e1-9b37-3efc7fc6d415
-- title:
--   Hermitek LEAN: h k expansion perp phi0
-- statement:
--   Orthogonality to `Phi k 0` yields an expansion with vanishing zero mode.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L3458-L3468
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L3458-L3468

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

theorem HermitekLEAN.h_k_expansion_perp_phi0 :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        weightedInner G (Phi k 0) = 0 →
          ∃ g : ℕ → ℂ,
            G = hermiteSeries k g ∧
              g 0 = 0 := by sorry
