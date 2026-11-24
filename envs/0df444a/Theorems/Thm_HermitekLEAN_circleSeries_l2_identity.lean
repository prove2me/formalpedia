-- Prove2me | Theorems.Thm_HermitekLEAN_circleSeries_l2_identity
-- name    : HermitekLEAN.circleSeries_l2_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:31:01.664234+00:00
-- url     : https://prove2.me/theorems/de827334-a9cc-4108-95d0-c88010004e41
-- title:
--   Hermitek LEAN: circle Series l2 identity
-- statement:
--   Compatibility statement: circle Parseval identity for an `H_k` expansion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L3267-L3363
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L3267-L3363

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

theorem HermitekLEAN.circleSeries_l2_identity :
    ∀ {k : ℕ} {G : ℂ → ℂ} {g : ℕ → ℂ},
      G ∈ Hk k →
        G = hermiteSeries k g →
          Summable (fun n => ‖g n‖ ^ 2) →
          ∀ r : ℝ,
            0 < r →
              circleL2Sq (circleSeries k g r) =
                ∑' n : ℕ, ‖g n‖ ^ 2 * |qkn k n r| ^ 2 := by sorry
