-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_groupCohomologyULiftIntAddEquiv_map_subtype
-- name    : GroundTheory.ProfCoh.groupCohomologyULiftIntAddEquiv_map_subtype
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:51:00.832789+00:00
-- url     : https://prove2.me/theorems/a6ca6722-c573-4f78-956d-61d735e92d19
-- title:
--   Prof Coh: group Cohomology ULift Int Add Equiv map subtype
-- statement:
--   The Prof Coh construction uses the group Cohomology ULift Int Add Equiv map subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalClassFormation/FiniteVanishing/IntScalars.lean#L94-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalClassFormation/FiniteVanishing/IntScalars.lean#L94-L107

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalClassFormation_FiniteVanishing_IntScalars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory Limits groupCohomology
variable {Γ : Type} [Group Γ]

theorem GroundTheory.ProfCoh.groupCohomologyULiftIntAddEquiv_map_subtype (M : Rep.{0} (ULift.{0} ℤ) Γ) (S : Subgroup Γ)
    (n : ℕ) (x : groupCohomology M n) :
    groupCohomologyULiftIntAddEquiv (Rep.res S.subtype M) n
        ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) n).hom x) =
      (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (uliftIntToIntRep M))) n).hom
        (groupCohomologyULiftIntAddEquiv M n x) := by sorry
