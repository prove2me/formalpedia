-- Prove2me | Theorems.Thm_GlobalTheory_InertField_isField_of_inert
-- name    : GlobalTheory.InertField.isField_of_inert
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:08:26.973515+00:00
-- url     : https://prove2.me/theorems/f609b2b4-ccce-419d-8eea-b0708b8f71c1
-- title:
--   Inert Field: is Field of inert
-- statement:
--   The Inert Field construction uses the is Field of inert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsFieldAdicCompletionTensorOfInert.lean#L226-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsFieldAdicCompletionTensorOfInert.lean#L226-L370

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

theorem GlobalTheory.InertField.isField_of_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ v : HeightOneSpectrum (𝓞 F), (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime → IsField (v.adicCompletion F ⊗[F] E) := by sorry
