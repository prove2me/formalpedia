-- Prove2me | Theorems.Thm_HermitekLEAN_qkn_top_term_limit
-- name    : HermitekLEAN.qkn_top_term_limit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:29:55.879545+00:00
-- url     : https://prove2.me/theorems/c739ff9d-0af6-408a-b192-4f276edb8249
-- title:
--   Hermitek LEAN: qkn top term limit
-- statement:
--   After dividing by `r^n`, `qkn k n r` converges to its explicit top term.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L559-L571
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L559-L571

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

theorem HermitekLEAN.qkn_top_term_limit :
    ∀ k n : ℕ,
      ∀ ε : ℝ,
        0 < ε →
          ∃ R0 : ℝ,
            1 ≤ R0 ∧
              ∀ r : ℝ,
                R0 ≤ r →
                  ‖(qkn k n r : ℂ) / (r ^ n : ℂ) -
                      ((1 / Real.sqrt (Nat.factorial n : ℝ) : ℝ) : ℂ)‖ ≤ ε := by sorry
