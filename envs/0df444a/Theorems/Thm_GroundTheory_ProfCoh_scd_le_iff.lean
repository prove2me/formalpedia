-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_scd_le_iff
-- name    : GroundTheory.ProfCoh.scd_le_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:50:32.100647+00:00
-- url     : https://prove2.me/theorems/e58a4de7-c24f-413e-babb-35aec7dc76b9
-- title:
--   Prof Coh: scd le iff
-- statement:
--   The Prof Coh construction uses the scd le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/PrimaryComponentCohomologyEqBotOfScdpLt.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/PrimaryComponentCohomologyEqBotOfScdpLt.lean#L46-L48

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

theorem GroundTheory.ProfCoh.scd_le_iff {n : ℕ∞} : scd G ≤ n ↔ ∀ p : ℕ, p.Prime → scdp p G ≤ n := by sorry
