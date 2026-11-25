-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_eq_zero_of_pow_nsmul_eq_zero
-- name    : GroundTheory.ProfCoh.eq_zero_of_pow_nsmul_eq_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:45:25.437265+00:00
-- url     : https://prove2.me/theorems/858d77c4-1933-4a6f-af3c-a1b5506231ee
-- title:
--   Prof Coh: eq zero of pow nsmul eq zero
-- statement:
--   The Prof Coh construction uses the eq zero of pow nsmul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L121-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L121-L129

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

theorem GroundTheory.ProfCoh.eq_zero_of_pow_nsmul_eq_zero {M : Type*} [AddCommMonoid M] {p : ℕ}
    (hp : ∀ x : M, p • x = 0 → x = 0) (k : ℕ) (x : M) (hx : p ^ k • x = 0) : x = 0 := by sorry
