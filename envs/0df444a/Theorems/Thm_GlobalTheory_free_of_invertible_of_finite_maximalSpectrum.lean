-- Prove2me | Theorems.Thm_GlobalTheory_free_of_invertible_of_finite_maximalSpectrum
-- name    : GlobalTheory.free_of_invertible_of_finite_maximalSpectrum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:02.1658+00:00
-- url     : https://prove2.me/theorems/a5cee41a-fd02-4a3f-9772-9a6c6d142bfa
-- title:
--   Global Theory: free of invertible of finite maximal Spectrum
-- statement:
--   The Global Theory construction uses the free of invertible of finite maximal Spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L566-L569
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L566-L569

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable {A : Type*} [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module A M]

theorem GlobalTheory.free_of_invertible_of_finite_maximalSpectrum (A M : Type*) [CommRing A] [AddCommGroup M]
    [Module A M] [Finite (MaximalSpectrum A)] [Module.Invertible A M] : Module.Free A M := by sorry
