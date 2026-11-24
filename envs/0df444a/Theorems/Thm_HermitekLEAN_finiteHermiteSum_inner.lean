-- Prove2me | Theorems.Thm_HermitekLEAN_finiteHermiteSum_inner
-- name    : HermitekLEAN.finiteHermiteSum_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:00:09.967122+00:00
-- url     : https://prove2.me/theorems/0753ac92-3247-4f04-b24c-ea199ec28471
-- title:
--   Hermitek LEAN: finite Hermite Sum inner
-- statement:
--   Inner products of finite Hermite sums are finite coefficient inner products.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1646-L1675
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1646-L1675

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

theorem HermitekLEAN.finiteHermiteSum_inner :
    ∀ {k D : ℕ} (a b : Fin D → ℂ),
      weightedInner (finiteHermiteSum k a) (finiteHermiteSum k b) =
        ∑ n : Fin D, a n * star (b n) := by sorry
