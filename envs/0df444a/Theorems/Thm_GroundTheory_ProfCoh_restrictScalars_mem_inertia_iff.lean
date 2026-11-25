-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_restrictScalars_mem_inertia_iff
-- name    : GroundTheory.ProfCoh.restrictScalars_mem_inertia_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:51:00.502872+00:00
-- url     : https://prove2.me/theorems/5468379f-7d94-468d-b1b2-6faf9caf2076
-- title:
--   Prof Coh: restrict Scalars mem inertia iff
-- statement:
--   The Prof Coh construction uses the restrict Scalars mem inertia iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Ramification.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Ramification.lean#L26-L28

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

theorem GroundTheory.ProfCoh.restrictScalars_mem_inertia_iff (Q : Ideal (𝓞 M)) (σ : Gal(M/E)) :
    AlgEquiv.restrictScalarsHom F σ ∈ Q.inertia Gal(M/F) ↔ σ ∈ Q.inertia Gal(M/E) := by sorry
