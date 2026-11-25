-- Prove2me | Theorems.Thm_GlobalTheory_powGr_map_mk
-- name    : GlobalTheory.powGr.map_mk
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:49:21.530488+00:00
-- url     : https://prove2.me/theorems/0489f2bc-26e4-5630-8592-72a79d063015
-- title:
--   pow Gr: map mk
-- statement:
--   The pow Gr construction uses the map mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L179-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L179-L182

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
variable {R : Type*} [CommRing R]
open GlobalTheory.powGr
variable (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] (a : ℕ)
variable {I M a}

theorem GlobalTheory.powGr.map_mk {N : Type*} [AddCommGroup N] [Module R N] (g : M →ₗ[R] N)
    (x : ↥(I ^ a • ⊤ : Submodule R M)) :
    map I a g (mk I M a x) =
      mk I N a ⟨g x, Submodule.smul_top_le_comap_smul_top (I ^ a) g x.2⟩ := by sorry
