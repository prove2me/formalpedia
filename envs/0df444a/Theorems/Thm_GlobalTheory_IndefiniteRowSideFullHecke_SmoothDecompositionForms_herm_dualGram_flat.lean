-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SmoothDecompositionForms_herm_dualGram_flat
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms.herm_dualGram_flat
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:10:05.16464+00:00
-- url     : https://prove2.me/theorems/8e1c7362-f70d-4861-9e8c-8db77c5d0e2e
-- title:
--   Smooth Decomposition Forms: herm dual Gram flat
-- statement:
--   The Smooth Decomposition Forms construction uses the herm dual Gram flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SmoothDecompositionForms.lean#L168-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SmoothDecompositionForms.lean#L168-L174

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms.herm_dualGram_flat [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : Aᴴ = A) (h2 : A * A = 1) (y y' : ι → ℂ) :
    herm (dualGram A) (flat A y) (flat A y') = herm A y' y := by sorry
