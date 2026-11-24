-- Prove2me | Theorems.Thm_GlobalTheory_NormUnits_fg_quot_intUnits
-- name    : GlobalTheory.NormUnits.fg_quot_intUnits
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:36:34.428469+00:00
-- url     : https://prove2.me/theorems/615df047-f9aa-4872-9495-9203dff3ecec
-- title:
--   Norm Units: fg quot int Units
-- statement:
--   The Norm Units construction uses the fg quot int Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFinsetCosetsIntegralNormUnits.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFinsetCosetsIntegralNormUnits.lean#L10-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfSeparableMarkedCharpolyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FgUnitsQuotIntegralUnitsFiniteFieldExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FgUnitsQuotIntegralUnitsReducedFiniteAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinsetCosetsIntegralNormUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.NormUnits

theorem GlobalTheory.NormUnits.fg_quot_intUnits : ∀ (K : UQ) (B : InvAlg K), B.P.Separable →
    Group.FG (B.Aˣ ⧸ intUnits K.O B.A) := by sorry
