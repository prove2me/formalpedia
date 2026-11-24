-- Prove2me | Theorems.Thm_GlobalTheory_PosSemidefShiftByScalar_main
-- name    : GlobalTheory.PosSemidefShiftByScalar.main
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:45.331153+00:00
-- url     : https://prove2.me/theorems/c96488eb-2274-488e-be5b-8f6bda82965b
-- title:
--   Pos Semidef Shift By Scalar: main
-- statement:
--   The Pos Semidef Shift By Scalar construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/PosSemidefSubSmulOne.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/PosSemidefSubSmulOne.lean#L39-L41

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubSmulOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Unitary
open scoped ComplexOrder
open GlobalTheory GlobalTheory.PosSemidefShiftByScalar

theorem GlobalTheory.PosSemidefShiftByScalar.main : ∀ {N : ℕ} {E : Type} [inst : Field E] (Ψ : Finset (E →+* ℂ)) {Z : GlobalTheory.SW.CM Ψ N N},
    Z ∈ GlobalTheory.SW.Hn Ψ N → ∃ (δ : ℝ), (0 : ℝ) < δ ∧ Z ∈ GlobalTheory.SW.HnGe Ψ N δ := by sorry
