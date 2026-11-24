-- Prove2me | Theorems.Thm_GlobalTheory_JR_Spec_isIntegral_integer_of_spectralNorm_le_one
-- name    : GlobalTheory.JR.Spec.isIntegral_integer_of_spectralNorm_le_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:36:19.91219+00:00
-- url     : https://prove2.me/theorems/dca8ffa8-dc33-4c59-bdd1-7f773faf905e
-- title:
--   Spec: is Integral integer of spectral Norm le one
-- statement:
--   The Spec construction uses the is Integral integer of spectral Norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralOrInvIsIntegralFiniteExtUltrametric.lean#L14-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralOrInvIsIntegralFiniteExtUltrametric.lean#L14-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralOrInvIsIntegralFiniteExtUltrametric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open Polynomial
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Spec
variable {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F]
  {k : Type} [Field k] [Algebra F k]

theorem GlobalTheory.JR.Spec.isIntegral_integer_of_spectralNorm_le_one [FiniteDimensional F k] {y : k}
    (h : spectralNorm F k y ≤ 1) : IsIntegral (NormedField.valuation (K := F)).integer y := by sorry
