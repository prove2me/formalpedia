-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SmoothDecompositionForms_isSignedDecomp_trivial
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms.isSignedDecomp_trivial
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:09:57.244682+00:00
-- url     : https://prove2.me/theorems/9864fd35-436f-4cb7-9ee2-1b565a1cf6b8
-- title:
--   Smooth Decomposition Forms: is Signed Decomp trivial
-- statement:
--   The Smooth Decomposition Forms construction uses the is Signed Decomp trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SmoothDecompositionForms.lean#L230-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SmoothDecompositionForms.lean#L230-L265

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms.isSignedDecomp_trivial [DecidableEq ι] (R : HRep k r) (ep : ι → ℝ) (hep : ∀ c, ep c = 1 ∨ ep c = -1) :
    IsSignedDecomp (fun _ => (1 : Matrix ι ι ℂ)) (Matrix.diagonal fun c => (ep c : ℂ)) R (fun _ : ι => R)
      (fun j v => Pi.single j v) (fun j x => x j) ep := by sorry
