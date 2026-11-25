-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_mem_gsOpenSubgroup_iff
-- name    : GroundTheory.ProfCoh.mem_gsOpenSubgroup_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:02:10.62095+00:00
-- url     : https://prove2.me/theorems/13e16b1e-64d7-59c0-847d-e6896f79f270
-- title:
--   Prof Coh: mem gs Open Subgroup iff
-- statement:
--   The Prof Coh construction uses the mem gs Open Subgroup iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseChangeDefs.lean#L292-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseChangeDefs.lean#L292-L294

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_BaseChangeDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain
universe u
noncomputable section
variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))
  (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S)

theorem GroundTheory.ProfCoh.mem_gsOpenSubgroup_iff (σ : galUnramifiedOutside F Ω S) :
    σ ∈ gsOpenSubgroup S hL ↔ ∀ x : L, σ (gsEmbedding hL x) = gsEmbedding hL x := by sorry
