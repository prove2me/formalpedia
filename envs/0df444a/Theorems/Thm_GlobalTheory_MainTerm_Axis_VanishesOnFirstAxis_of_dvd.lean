-- Prove2me | Theorems.Thm_GlobalTheory_MainTerm_Axis_VanishesOnFirstAxis_of_dvd
-- name    : GlobalTheory.MainTerm.Axis.VanishesOnFirstAxis.of_dvd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:33:44.150814+00:00
-- url     : https://prove2.me/theorems/e6056a13-6904-4cb9-87bc-3477c9fc306b
-- title:
--   Vanishes On First Axis: of dvd
-- statement:
--   The Vanishes On First Axis construction uses the of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffLeafGaugeSubMainTermEqZeroOnFirstAxis.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffLeafGaugeSubMainTermEqZeroOnFirstAxis.lean#L48-L52

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffLeafGaugeSubMainTermEqZeroOnFirstAxis
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

theorem GlobalTheory.MainTerm.Axis.VanishesOnFirstAxis.of_dvd {F G : MvPowerSeries (ι ⊕ ι') C} (h : VanishesOnFirstAxis F)
    (hd : F ∣ G) : VanishesOnFirstAxis G := by sorry
