-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_IsTopologicalGenerator_eq_of_forall_zpow_pi
-- name    : GroundTheory.ProfCoh.IsTopologicalGenerator.eq_of_forall_zpow_pi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:26.116082+00:00
-- url     : https://prove2.me/theorems/20aad4e2-93f2-4b12-8fd4-ba9be729734f
-- title:
--   Is Topological Generator: eq of forall zpow pi
-- statement:
--   The Is Topological Generator construction uses the eq of forall zpow pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ProcyclicDefs.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ProcyclicDefs.lean#L34-L42

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

theorem GroundTheory.ProfCoh.IsTopologicalGenerator.eq_of_forall_zpow_pi (hσ : IsTopologicalGenerator σ) {n : ℕ} {Y : Type*}
    {f g : (Fin n → G) → Y} (hf : IsLocallyConstant f) (hg : IsLocallyConstant g)
    (h : ∀ m : Fin n → ℤ, f (fun i => σ ^ m i) = g (fun i => σ ^ m i)) : f = g := by sorry
