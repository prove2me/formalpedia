-- Prove2me | Theorems.Thm_GlobalTheory_MainTerm_Axis_VanishesOnFirstAxis_sum
-- name    : GlobalTheory.MainTerm.Axis.VanishesOnFirstAxis.sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:32:38.04831+00:00
-- url     : https://prove2.me/theorems/b21beb10-2b8e-44af-b441-1c89e2c1ff3e
-- title:
--   Vanishes On First Axis: sum
-- statement:
--   The Vanishes On First Axis construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffLeafGaugeSubMainTermEqZeroOnFirstAxis.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffLeafGaugeSubMainTermEqZeroOnFirstAxis.lean#L33-L37

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffLeafGaugeSubMainTermEqZeroOnFirstAxis
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open GlobalTheory GlobalTheory.MainTerm GlobalTheory.MainTerm.Axis
variable {C : Type} [Field C] {ι ι' : Type}

theorem GlobalTheory.MainTerm.Axis.VanishesOnFirstAxis.sum {α : Type} (s : Finset α) {F : α → MvPowerSeries (ι ⊕ ι') C}
    (h : ∀ x, VanishesOnFirstAxis (F x)) : VanishesOnFirstAxis (∑ x ∈ s, F x) := by sorry
