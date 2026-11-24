-- Prove2me | Theorems.Thm_HermitekLEAN_h_k_expansion
-- name    : HermitekLEAN.h_k_expansion
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:30:48.822204+00:00
-- url     : https://prove2.me/theorems/28c3aec3-6b27-4c1a-9eec-ce3e53dcef21
-- title:
--   Hermitek LEAN: h k expansion
-- statement:
--   Every `G ∈ H_k` admits a Hermite expansion with Parseval.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2936-L2943
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2936-L2943

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

theorem HermitekLEAN.h_k_expansion :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        ∃ g : ℕ → ℂ,
          G = hermiteSeries k g ∧
            weightedNormSq G = ∑' n : ℕ, ‖g n‖ ^ 2 := by sorry
