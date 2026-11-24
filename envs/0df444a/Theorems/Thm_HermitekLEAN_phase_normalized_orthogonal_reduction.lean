-- Prove2me | Theorems.Thm_HermitekLEAN_phase_normalized_orthogonal_reduction
-- name    : HermitekLEAN.phase_normalized_orthogonal_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:32:12.046395+00:00
-- url     : https://prove2.me/theorems/d47d1d8d-7faa-46f7-b30c-66a25f1082fb
-- title:
--   Hermitek LEAN: phase normalized orthogonal reduction
-- statement:
--   Imported phase-normalized orthogonal reduction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/ImportedAnalyticInputs.lean#L54-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/ImportedAnalyticInputs.lean#L54-L74

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_ImportedAnalyticInputs
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ImportedAnalyticInputs
public import Theorems.Thm_HermiteLEAN_phase_normalized_orthogonal_reduction

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators
noncomputable section
open HermitekLEAN

theorem HermitekLEAN.phase_normalized_orthogonal_reduction
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (defect : H → ℝ)
    (hdefect_nonneg : ∀ h : H, 0 ≤ defect h)
    (f0 : H)
    (hf0 : ‖f0‖ = 1)
    (C : ℝ)
    (hC : 0 < C)
    (horth : ∀ g : H, inner ℂ g f0 = (0 : ℂ) → ‖g‖ ≤ C * defect g)
    (hscalar :
      ∀ h : H, (inner ℂ h f0).im = 0 →
        |(2 : ℝ) * (inner ℂ h f0).re + ‖h‖ ^ 2| ≤ defect h * (2 + ‖h‖))
    (hcompare :
      ∀ h : H, ∀ a : ℝ, defect (h - (a : ℂ) • f0) ≤ |a| + defect h) :
    ∃ δ Mloc : ℝ, 0 < δ ∧ 0 < Mloc ∧
      ∀ h : H, ‖h‖ ≤ δ → (inner ℂ h f0).im = 0 → ‖h‖ ≤ Mloc * defect h := by sorry
