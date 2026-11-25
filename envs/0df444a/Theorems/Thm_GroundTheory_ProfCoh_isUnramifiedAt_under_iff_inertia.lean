-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedAt_under_iff_inertia
-- name    : GroundTheory.ProfCoh.isUnramifiedAt_under_iff_inertia
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:50:40.84246+00:00
-- url     : https://prove2.me/theorems/fab36af5-47bf-44e8-8c39-1d03bbd23b3e
-- title:
--   Prof Coh: is Unramified At under iff inertia
-- statement:
--   The Prof Coh construction uses the is Unramified At under iff inertia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Ramification.lean#L41-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Ramification.lean#L41-L86

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
variable [NumberField F] [NumberField E] [NumberField M] [IsGalois F M]

theorem GroundTheory.ProfCoh.isUnramifiedAt_under_iff_inertia (Q : Ideal (𝓞 M)) [Q.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 F) (Q.under (𝓞 E)) ↔
      ∀ σ ∈ Q.inertia Gal(M/F), ∀ x : E, σ (algebraMap E M x) = algebraMap E M x := by sorry
