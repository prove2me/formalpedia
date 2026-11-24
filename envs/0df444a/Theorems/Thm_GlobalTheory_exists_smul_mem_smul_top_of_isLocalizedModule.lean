-- Prove2me | Theorems.Thm_GlobalTheory_exists_smul_mem_smul_top_of_isLocalizedModule
-- name    : GlobalTheory.exists_smul_mem_smul_top_of_isLocalizedModule
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:34.023827+00:00
-- url     : https://prove2.me/theorems/fd53411d-1c09-49d5-9c0c-7151d8d39374
-- title:
--   Global Theory: exists smul mem smul top of is Localized Module
-- statement:
--   The Global Theory construction uses the exists smul mem smul top of is Localized Module property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L621-L634
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L621-L634

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (S : Type*) [CommRing S] [Algebra R S]
variable {N : Type*} [AddCommGroup N] [Module R N]

theorem GlobalTheory.exists_smul_mem_smul_top_of_isLocalizedModule (T : Submonoid R) (g : M →ₗ[R] N)
    [IsLocalizedModule T g] (J : Ideal R) {x : M} (hx : g x ∈ (J • ⊤ : Submodule R N)) :
    ∃ s ∈ T, s • x ∈ (J • ⊤ : Submodule R M) := by sorry
