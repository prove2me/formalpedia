-- Prove2me | Theorems.Thm_GlobalTheory_IwahoriInj_exists_flip
-- name    : GlobalTheory.IwahoriInj.exists_flip
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:23:41.484796+00:00
-- url     : https://prove2.me/theorems/65b7c367-e674-47b9-bbd2-3e160d8e01a4
-- title:
--   Iwahori Inj: exists flip
-- statement:
--   The Iwahori Inj construction uses the exists flip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L205-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L205-L260

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.IwahoriInj
variable {n : Type}

theorem GlobalTheory.IwahoriInj.exists_flip {f : n → n → ℤ} (hf : Chamber f) {i j : n} (hij : i ≠ j)
    (hw : ∀ l, l ≠ i → l ≠ j → f j i < f j l + f l i) :
    ∃ g f' : n → n → ℤ, Conc g ∧ Chamber f' ∧ f i j = g i j + 1 ∧
      (∀ a b, ¬ (a = i ∧ b = j) → f a b = g a b) ∧ f' j i = g j i + 1 ∧
      (∀ a b, ¬ (a = j ∧ b = i) → f' a b = g a b) := by sorry
