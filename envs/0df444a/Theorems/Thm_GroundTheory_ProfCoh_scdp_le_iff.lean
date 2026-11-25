-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_scdp_le_iff
-- name    : GroundTheory.ProfCoh.scdp_le_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:51:33.629809+00:00
-- url     : https://prove2.me/theorems/680d8f10-7930-4812-a3d5-57a832db6d62
-- title:
--   Prof Coh: scdp le iff
-- statement:
--   The Prof Coh construction uses the scdp le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/PrimaryComponentCohomologyEqBotOfScdpLt.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/PrimaryComponentCohomologyEqBotOfScdpLt.lean#L34-L39

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

theorem GroundTheory.ProfCoh.scdp_le_iff {n : ℕ∞} :
    scdp p G ≤ n ↔ ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A],
      ∀ q : ℕ, n < q → AddCommGroup.primaryComponent (cohomology A q) p = ⊥ := by sorry
