-- Prove2me | Theorems.Thm_GlobalTheory_isSaturatedSubmodule_iff_localized_maximal
-- name    : GlobalTheory.isSaturatedSubmodule_iff_localized_maximal
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:47:54.059647+00:00
-- url     : https://prove2.me/theorems/e00c2cf7-47c1-5c8d-93cb-d15ea3292908
-- title:
--   Global Theory: is Saturated Submodule iff localized maximal
-- statement:
--   The Global Theory construction uses the is Saturated Submodule iff localized maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L634-L646
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L634-L646

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

theorem GlobalTheory.isSaturatedSubmodule_iff_localized_maximal [IsDomain R] {N : Submodule R M} :
    IsSaturatedSubmodule N ↔
      ∀ (P : Ideal R) [P.IsMaximal], IsSaturatedSubmodule (N.localized P.primeCompl) := by sorry
