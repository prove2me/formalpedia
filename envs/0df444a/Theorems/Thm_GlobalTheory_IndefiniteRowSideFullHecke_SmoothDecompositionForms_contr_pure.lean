-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SmoothDecompositionForms_contr_pure
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms.contr_pure
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:09:37.472604+00:00
-- url     : https://prove2.me/theorems/1556fc12-9bbb-412a-9a06-54786f8515ae
-- title:
--   Smooth Decomposition Forms: contr pure
-- statement:
--   The Smooth Decomposition Forms construction uses the contr pure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SmoothDecompositionForms.lean#L159-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SmoothDecompositionForms.lean#L159-L161

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_BesselMapUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SmoothDecompositionForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
open PI.UpqRep
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms
attribute [instance] HRep.instNorm HRep.instInner HRep.instComplete
variable {k r : ℕ}
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms.contr_pure (A : Matrix ι ι ℂ) (ω a : ι → ℂ) {E : Type} [AddCommGroup E] [Module ℂ E] (v : E) :
    contr A ω (pureT a v) = herm A a ω • v := by sorry
