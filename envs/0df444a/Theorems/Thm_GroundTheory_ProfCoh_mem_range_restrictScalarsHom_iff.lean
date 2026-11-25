-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_mem_range_restrictScalarsHom_iff
-- name    : GroundTheory.ProfCoh.mem_range_restrictScalarsHom_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:50:56.495442+00:00
-- url     : https://prove2.me/theorems/9b5064b4-a72e-47b5-a748-77e061c35968
-- title:
--   Prof Coh: mem range restrict Scalars Hom iff
-- statement:
--   The Prof Coh construction uses the mem range restrict Scalars Hom iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Ramification.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Ramification.lean#L30-L37

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Ramification
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
variable {F E M : Type*} [Field F] [Field E] [Field M] [Algebra F E] [Algebra E M] [Algebra F M]
  [IsScalarTower F E M]

theorem GroundTheory.ProfCoh.mem_range_restrictScalarsHom_iff (σ : Gal(M/F)) :
    σ ∈ (AlgEquiv.restrictScalarsHom F : Gal(M/E) →* Gal(M/F)).range ↔
      ∀ x : E, σ (algebraMap E M x) = algebraMap E M x := by sorry
