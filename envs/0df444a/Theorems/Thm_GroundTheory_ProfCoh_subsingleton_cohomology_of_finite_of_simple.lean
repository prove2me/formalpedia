-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_subsingleton_cohomology_of_finite_of_simple
-- name    : GroundTheory.ProfCoh.subsingleton_cohomology_of_finite_of_simple
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:46:38.183924+00:00
-- url     : https://prove2.me/theorems/583fb40e-825a-4c37-86b9-8a79500cabee
-- title:
--   Prof Coh: subsingleton cohomology of finite of simple
-- statement:
--   The Prof Coh construction uses the subsingleton cohomology of finite of simple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L263-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L263-L345

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

theorem GroundTheory.ProfCoh.subsingleton_cohomology_of_finite_of_simple {p : ℕ} {m : ℕ}
    (h : ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A], IsSimpleOrder (Subrepresentation A.ρ) →
      (∀ a : A, p • a = 0) → Subsingleton (cohomology A m))
    (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A] [Finite A]
    (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0) : Subsingleton (cohomology A m) := by sorry
