-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SmoothDecompositionForms_tensForm_pure
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms.tensForm_pure
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:09:50.489031+00:00
-- url     : https://prove2.me/theorems/e568b9f6-a3f5-4484-89fa-01367798f006
-- title:
--   Smooth Decomposition Forms: tens Form pure
-- statement:
--   The Smooth Decomposition Forms construction uses the tens Form pure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SmoothDecompositionForms.lean#L153-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SmoothDecompositionForms.lean#L153-L157

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms.tensForm_pure (A : Matrix ι ι ℂ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a b : ι → ℂ) (v w : H) : tensForm A (pureT a v) (pureT b w) = herm A a b * ⟪w, v⟫_ℂ := by sorry
