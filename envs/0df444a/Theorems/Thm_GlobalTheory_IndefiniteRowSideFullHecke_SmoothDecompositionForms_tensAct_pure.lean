-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SmoothDecompositionForms_tensAct_pure
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms.tensAct_pure
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:09:59.387496+00:00
-- url     : https://prove2.me/theorems/cf08e12b-6adc-475d-bdf6-a2091a7ba53b
-- title:
--   Smooth Decomposition Forms: tens Act pure
-- statement:
--   The Smooth Decomposition Forms construction uses the tens Act pure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SmoothDecompositionForms.lean#L163-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SmoothDecompositionForms.lean#L163-L166

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms.tensAct_pure (ρ : Mx k r → Matrix ι ι ℂ) (R : HRep k r) (g : Mx k r) (a : ι → ℂ) (v : R.H) :
    tensAct ρ R g (pureT a v) = pureT (ρ g *ᵥ a) (R.σ g v) := by sorry
