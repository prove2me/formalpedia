-- Prove2me | Theorems.Thm_GlobalTheory_T_comap_eq_of_continuous_adicCompletion_iso
-- name    : GlobalTheory.T.comap_eq_of_continuous_adicCompletion_iso
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:30:40.333524+00:00
-- url     : https://prove2.me/theorems/8c3ea8af-1949-48a4-97b8-4c78b87da4ea
-- title:
--   T: comap eq of continuous adic Completion iso
-- statement:
--   The T construction uses the comap eq of continuous adic Completion iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ComapEqOfContinuousAdicCompletionIsoStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ComapEqOfContinuousAdicCompletionIsoStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapEqOfContinuousAdicCompletionIso
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapEqOfContinuousAdicCompletionIsoStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.comap_eq_of_continuous_adicCompletion_iso : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')) (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i → (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) → w'.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = w.asIdeal := by sorry
