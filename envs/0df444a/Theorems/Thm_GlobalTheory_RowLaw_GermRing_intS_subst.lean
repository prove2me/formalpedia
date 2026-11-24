-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_GermRing_intS_subst
-- name    : GlobalTheory.RowLaw.GermRing.intS_subst
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:55:34.969801+00:00
-- url     : https://prove2.me/theorems/85243389-7388-41c3-a71e-4121a03ab82c
-- title:
--   Germ Ring: int S subst
-- statement:
--   The Germ Ring construction uses the int S subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGermEqGaugedFormalGroupLawExpIntegral.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGermEqGaugedFormalGroupLawExpIntegral.lean#L24-L28

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGermEqGaugedFormalGroupLawExpIntegral
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.FormalInv MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GermRing
variable {C : Type} [Field C]

theorem GlobalTheory.RowLaw.GermRing.intS_subst {V : VF C} {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (h0 : ∀ s, constantCoeff (a s) = 0) (ha : ∀ s, IntS V (a s)) {f : MvPowerSeries σ C} (hf : IntS V f) :
    IntS V (subst a f) := by sorry
