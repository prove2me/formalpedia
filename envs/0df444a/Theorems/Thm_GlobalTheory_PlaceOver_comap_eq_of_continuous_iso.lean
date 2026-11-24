-- Prove2me | Theorems.Thm_GlobalTheory_PlaceOver_comap_eq_of_continuous_iso
-- name    : GlobalTheory.PlaceOver.comap_eq_of_continuous_iso
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:44:31.607815+00:00
-- url     : https://prove2.me/theorems/72e4a016-bf8f-4a6e-9b12-bb6699e0099a
-- title:
--   Place Over: comap eq of continuous iso
-- statement:
--   The Place Over construction uses the comap eq of continuous iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ComapEqOfContinuousAdicCompletionIso.lean#L46-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ComapEqOfContinuousAdicCompletionIso.lean#L46-L64

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapEqOfContinuousAdicCompletionIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.PlaceOver

theorem GlobalTheory.PlaceOver.comap_eq_of_continuous_iso : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'))
    (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i →
    (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) →
    w'.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = w.asIdeal := by sorry
