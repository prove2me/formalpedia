-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_subrepCohomology_map
-- name    : GroundTheory.ProfCoh.subrepCohomology_map
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:02:52.263255+00:00
-- url     : https://prove2.me/theorems/82bd227d-1f5c-533c-bd6d-e9adbab44a6d
-- title:
--   Prof Coh: subrep Cohomology map
-- statement:
--   The Prof Coh construction uses the subrep Cohomology map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ColimitUnion.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ColimitUnion.lean#L66-L69

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_FilteredHomology
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
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
variable {k G : Type u} [CommRing k] [Group G]
variable (A : Rep.{u} k G) {ι : Type u} [Preorder ι] (W : ι → Submodule k A) (hW : Monotone W)
  (hstable : ∀ i g, W i ≤ (W i).comap (A.ρ g))
variable [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep A]

theorem GroundTheory.ProfCoh.subrepCohomology_map (n : ℕ) {i j : ι} (h : i ⟶ j) :
    (subrepCohomology A W hW hstable n).map h =
      cohomologyMap (subrepInclusion A W hW hstable (leOfHom h)) n := by sorry
