-- Prove2me | Theorems.Thm_GlobalTheory_LowerSubst_subst_int_on_lower
-- name    : GlobalTheory.LowerSubst.subst_int_on_lower
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:34:31.032159+00:00
-- url     : https://prove2.me/theorems/82f32e79-84ed-4401-ada7-5fbd95a766dd
-- title:
--   Lower Subst: subst int on lower
-- statement:
--   The Lower Subst construction uses the subst int on lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffIntegralOnExponentsSubstOfLowerSet.lean#L42-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffIntegralOnExponentsSubstOfLowerSet.lean#L42-L51

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

theorem GlobalTheory.LowerSubst.subst_int_on_lower :
    ∀ (C : Type) [Field C] (V : VF C) (σ τ : Type) [Fintype σ] [Fintype τ] (P : (σ →₀ ℕ) → Prop), (∀ μ ν, ν ≤ μ → P μ → P ν) → ∀ (γ : MvPowerSeries τ C) (T : τ → MvPowerSeries σ C), (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) → (∀ w, MvPowerSeries.constantCoeff (T w) = 0) → (∀ w μ, P μ → V.Ge 0 (MvPowerSeries.coeff μ (T w))) → ∀ μ, P μ → V.Ge 0 (MvPowerSeries.coeff μ (MvPowerSeries.subst T γ)) := by sorry
