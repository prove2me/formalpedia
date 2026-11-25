-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SmoothDecompositionForms_isFormRep_std
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms.isFormRep_std
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:10:04.322163+00:00
-- url     : https://prove2.me/theorems/fa6dfeef-8a17-4869-9315-4fbbc19ea777
-- title:
--   Smooth Decomposition Forms: is Form Rep std
-- statement:
--   The Smooth Decomposition Forms construction uses the is Form Rep std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SmoothDecompositionForms.lean#L204-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SmoothDecompositionForms.lean#L204-L219

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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms.isFormRep_std (k r : ℕ) : IsFormRep k r (stdRep k r) (Hpk k r) 1 := by sorry
