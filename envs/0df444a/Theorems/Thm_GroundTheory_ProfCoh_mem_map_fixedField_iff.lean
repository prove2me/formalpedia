-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_mem_map_fixedField_iff
-- name    : GroundTheory.ProfCoh.mem_map_fixedField_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:51:16.669408+00:00
-- url     : https://prove2.me/theorems/1b904e46-cb89-4a8d-99da-22d8a37ceac6
-- title:
--   Prof Coh: mem map fixed Field iff
-- statement:
--   The Prof Coh construction uses the mem map fixed Field iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Unramified.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Unramified.lean#L63-L70

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_MaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Ramification
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Unramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain
open scoped Pointwise
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
omit [NumberField F]

theorem GroundTheory.ProfCoh.mem_map_fixedField_iff {M : IntermediateField F Ω} (H : Subgroup Gal(M/F)) (x : Ω) :
    x ∈ (IntermediateField.fixedField H).map M.val ↔ ∃ hx : x ∈ M, ∀ σ ∈ H, σ ⟨x, hx⟩ = ⟨x, hx⟩ := by sorry
