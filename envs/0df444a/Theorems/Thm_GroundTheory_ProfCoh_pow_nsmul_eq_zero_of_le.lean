-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_pow_nsmul_eq_zero_of_le
-- name    : GroundTheory.ProfCoh.pow_nsmul_eq_zero_of_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:47:33.180252+00:00
-- url     : https://prove2.me/theorems/ec24911c-602e-4dc0-9843-6111f1e84e74
-- title:
--   Prof Coh: pow nsmul eq zero of le
-- statement:
--   The Prof Coh construction uses the pow nsmul eq zero of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L116-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L116-L119

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
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
open CategoryTheory Limits
universe u
attribute [local instance 2000] Rep.hV2
attribute [-instance] ULift.module
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem GroundTheory.ProfCoh.pow_nsmul_eq_zero_of_le {M : Type*} [AddCommMonoid M] {p k K : ℕ} {a : M} (h : k ≤ K)
    (ha : p ^ k • a = 0) : p ^ K • a = 0 := by sorry
