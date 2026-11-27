-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_primaryComponent_cohomology_eq_bot_of_cdp_lt
-- name    : GroundTheory.ProfCoh.primaryComponent_cohomology_eq_bot_of_cdp_lt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:02:46.963803+00:00
-- url     : https://prove2.me/theorems/f9b2e1f8-204f-4b09-bc98-c30fd4305835
-- title:
--   Prof Coh: primary Component cohomology eq bot of cdp lt
-- statement:
--   The Prof Coh construction uses the primary Component cohomology eq bot of cdp lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/PrimaryComponentCohomologyEqBotOfScdpLt.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/PrimaryComponentCohomologyEqBotOfScdpLt.lean#L41-L44

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
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
universe u
variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {p G}

theorem GroundTheory.ProfCoh.primaryComponent_cohomology_eq_bot_of_cdp_lt (A : Rep.{u} (ULift.{u} ℤ) G)
    [IsDiscreteRep A] (hA : IsAddTorsion A) {q : ℕ} (hq : cdp p G < q) :
    AddCommGroup.primaryComponent (cohomology A q) p = ⊥ := by sorry
