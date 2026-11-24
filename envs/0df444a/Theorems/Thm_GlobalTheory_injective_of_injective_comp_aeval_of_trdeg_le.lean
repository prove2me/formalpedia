-- Prove2me | Theorems.Thm_GlobalTheory_injective_of_injective_comp_aeval_of_trdeg_le
-- name    : GlobalTheory.injective_of_injective_comp_aeval_of_trdeg_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:55:14.649209+00:00
-- url     : https://prove2.me/theorems/eafe6a74-b230-4551-9f68-68bae372d6b7
-- title:
--   Global Theory: injective of injective comp aeval of trdeg le
-- statement:
--   The Global Theory construction uses the injective of injective comp aeval of trdeg le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/InjectiveOfInjectiveCompAevalOfTrdegLe.lean#L10-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/InjectiveOfInjectiveCompAevalOfTrdegLe.lean#L10-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_InjectiveOfInjectiveCompAevalOfTrdegLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open GlobalTheory
open MvPolynomial

theorem GlobalTheory.injective_of_injective_comp_aeval_of_trdeg_le {k A κ ι : Type} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [CommRing κ] [Finite ι] (b : ι → A)
    (hA : Algebra.trdeg k A ≤ Cardinal.mk ι) (χ : A →+* κ)
    (hχ : Function.Injective (fun q : MvPolynomial ι k => χ (aeval b q))) :
    Function.Injective χ := by sorry
