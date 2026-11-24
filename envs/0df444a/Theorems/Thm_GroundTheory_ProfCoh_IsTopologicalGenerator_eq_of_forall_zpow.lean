-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_IsTopologicalGenerator_eq_of_forall_zpow
-- name    : GroundTheory.ProfCoh.IsTopologicalGenerator.eq_of_forall_zpow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:36:41.971888+00:00
-- url     : https://prove2.me/theorems/9153ff68-fc70-458f-b717-14513689c2d7
-- title:
--   Is Topological Generator: eq of forall zpow
-- statement:
--   The Is Topological Generator construction uses the eq of forall zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ProcyclicDefs.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ProcyclicDefs.lean#L29-L32

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ProcyclicDefs
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
variable {G : Type*} [Group G] [TopologicalSpace G]
open GroundTheory.ProfCoh.IsTopologicalGenerator
variable {σ : G}

theorem GroundTheory.ProfCoh.IsTopologicalGenerator.eq_of_forall_zpow (hσ : IsTopologicalGenerator σ) {Y : Type*} {f g : G → Y}
    (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) (h : ∀ n : ℤ, f (σ ^ n) = g (σ ^ n)) :
    f = g := by sorry
