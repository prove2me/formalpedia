-- Prove2me | Theorems.Thm_GlobalTheory_LowerSubst_intOn_mul
-- name    : GlobalTheory.LowerSubst.intOn_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:31:12.990163+00:00
-- url     : https://prove2.me/theorems/7fe23a58-d7c0-4310-8cc9-2c7894b0926d
-- title:
--   Lower Subst: int On mul
-- statement:
--   The Lower Subst construction uses the int On mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffIntegralOnExponentsSubstOfLowerSet.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffIntegralOnExponentsSubstOfLowerSet.lean#L24-L30

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffIntegralOnExponentsSubstOfLowerSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open GlobalTheory GlobalTheory.LowerSubst
open MvPowerSeries
variable {C : Type} [Field C] (V : VF C) {σ : Type} (P : (σ →₀ ℕ) → Prop)

theorem GlobalTheory.LowerSubst.intOn_mul (hP : ∀ μ ν, ν ≤ μ → P μ → P ν) {f g : MvPowerSeries σ C}
    (hf : IntOn V P f) (hg : IntOn V P g) : IntOn V P (f * g) := by sorry
