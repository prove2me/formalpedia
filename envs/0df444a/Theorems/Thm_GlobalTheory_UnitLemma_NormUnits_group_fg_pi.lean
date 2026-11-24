-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_NormUnits_group_fg_pi
-- name    : GlobalTheory.UnitLemma.NormUnits.group_fg_pi
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:27:15.085724+00:00
-- url     : https://prove2.me/theorems/8962365e-7c4a-4ed5-9bb2-f51db81f4222
-- title:
--   Norm Units: group fg pi
-- statement:
--   The Norm Units construction uses the group fg pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FgUnitsQuotIntegralUnitsReducedFiniteAlgebra.lean#L10-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FgUnitsQuotIntegralUnitsReducedFiniteAlgebra.lean#L10-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FgUnitsQuotIntegralUnitsReducedFiniteAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.NormUnits

theorem GlobalTheory.UnitLemma.NormUnits.group_fg_pi {ι : Type} [Finite ι] (G : ι → Type) [∀ i, CommGroup (G i)]
    (hG : ∀ i, Group.FG (G i)) : Group.FG (∀ i, G i) := by sorry
