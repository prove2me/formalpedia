-- Prove2me | Theorems.Thm_GlobalTheory_InertField_exists_not_congr
-- name    : GlobalTheory.InertField.exists_not_congr
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:15:12.415676+00:00
-- url     : https://prove2.me/theorems/32d58d27-e24e-4945-a762-61554f8f2560
-- title:
--   Inert Field: exists not congr
-- statement:
--   The Inert Field construction uses the exists not congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsFieldAdicCompletionTensorOfInert.lean#L59-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsFieldAdicCompletionTensorOfInert.lean#L59-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFieldAdicCompletionTensorOfInert
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial
open GlobalTheory GlobalTheory.InertField
open scoped TensorProduct
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial

theorem GlobalTheory.InertField.exists_not_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ a : 𝓞 E, ∀ r : 𝓞 F, a - algebraMap (𝓞 F) (𝓞 E) r ∉ v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) := by sorry
