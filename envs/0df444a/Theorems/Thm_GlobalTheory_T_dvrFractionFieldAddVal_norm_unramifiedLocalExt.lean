-- Prove2me | Theorems.Thm_GlobalTheory_T_dvrFractionFieldAddVal_norm_unramifiedLocalExt
-- name    : GlobalTheory.T.dvrFractionFieldAddVal_norm_unramifiedLocalExt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:32:41.407421+00:00
-- url     : https://prove2.me/theorems/c8ba8f00-a02b-4c15-9c1b-8b6ddb25d4a7
-- title:
--   T: dvr Fraction Field Add Val norm unramified Local Ext
-- statement:
--   The T construction uses the dvr Fraction Field Add Val norm unramified Local Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvrFractionFieldAddValNormUnramifiedLocalExtStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvrFractionFieldAddValNormUnramifiedLocalExtStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvrFractionFieldAddValNormUnramifiedLocalExt
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvrFractionFieldAddValNormUnramifiedLocalExtStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.dvrFractionFieldAddVal_norm_unramifiedLocalExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ y : K'.E, val K.O (@Algebra.norm K.E K'.E _ _ φ.toAlgebra y) = (d : ℤ) * val K'.O y := by sorry
