-- Prove2me | Theorems.Thm_GlobalTheory_Published_ComplexMultiplicationJSt_finrank_eq
-- name    : GlobalTheory.Published.ComplexMultiplicationJSt.finrank_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:50.143349+00:00
-- url     : https://prove2.me/theorems/8983076a-320e-4d5c-bfcc-378705239369
-- title:
--   Complex Multiplication JSt: finrank eq
-- statement:
--   The Complex Multiplication JSt construction uses the finrank eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/ComplexMultiplicationJPremises.lean#L131-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/ComplexMultiplicationJPremises.lean#L131-L140

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
open NumberField
open scoped nonZeroDivisors IntermediateField
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

theorem GlobalTheory.Published.ComplexMultiplicationJSt.finrank_eq
    (h : _root_.GlobalTheory.Published.ComplexMultiplicationJSt) [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) {H : IntermediateField K ℂ} (hH : _root_.GlobalTheory.Published.IsHilbertClassField H) :
    Module.finrank K H = classNumber K := by sorry
