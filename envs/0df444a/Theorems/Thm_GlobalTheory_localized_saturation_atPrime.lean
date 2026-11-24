-- Prove2me | Theorems.Thm_GlobalTheory_localized_saturation_atPrime
-- name    : GlobalTheory.localized_saturation_atPrime
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:07:51.511927+00:00
-- url     : https://prove2.me/theorems/1b442468-c9fd-4cf9-99b7-2ab2a19b6b6a
-- title:
--   Global Theory: localized saturation at Prime
-- statement:
--   The Global Theory construction uses the localized saturation at Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L630-L632
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L630-L632

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  (S : Type*) [CommRing S] [Algebra R S] (p : Submonoid R) [IsLocalization p S]
  {Mp : Type*} [AddCommGroup Mp] [Module R Mp] [Module S Mp] [IsScalarTower R S Mp]
  (f : M →ₗ[R] Mp) [IsLocalizedModule p f]

theorem GlobalTheory.localized_saturation_atPrime [IsDomain R] (P : Ideal R) [P.IsPrime] (N : Submodule R M) :
    (saturation N).localized P.primeCompl = saturation (N.localized P.primeCompl) := by sorry
