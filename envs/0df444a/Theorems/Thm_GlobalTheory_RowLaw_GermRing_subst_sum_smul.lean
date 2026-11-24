-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_GermRing_subst_sum_smul
-- name    : GlobalTheory.RowLaw.GermRing.subst_sum_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:55:43.900479+00:00
-- url     : https://prove2.me/theorems/e2149a1d-935b-4239-bfd4-e3a689d6efd3
-- title:
--   Germ Ring: subst sum smul
-- statement:
--   The Germ Ring construction uses the subst sum smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGermEqGaugedFormalGroupLawExpIntegral.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGermEqGaugedFormalGroupLawExpIntegral.lean#L41-L44

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

theorem GlobalTheory.RowLaw.GermRing.subst_sum_smul {σ τ ι : Type} {a : σ → MvPowerSeries τ C} (ha : HasSubst a) (s : Finset ι) (w : ι → C)
    (f : ι → MvPowerSeries σ C) : subst a (∑ i ∈ s, w i • f i) = ∑ i ∈ s, w i • subst a (f i) := by sorry
