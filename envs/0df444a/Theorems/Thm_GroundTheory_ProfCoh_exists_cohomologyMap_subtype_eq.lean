-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_exists_cohomologyMap_subtype_eq
-- name    : GroundTheory.ProfCoh.exists_cohomologyMap_subtype_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:49:54.859557+00:00
-- url     : https://prove2.me/theorems/341c840a-ff42-4e09-85bb-4d2271773e75
-- title:
--   Prof Coh: exists cohomology Map subtype eq
-- statement:
--   The Prof Coh construction uses the exists cohomology Map subtype eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ColimitUnion.lean#L125-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ColimitUnion.lean#L125-L131

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
variable [CompactSpace G]
include hW

theorem GroundTheory.ProfCoh.exists_cohomologyMap_subtype_eq [Nonempty ι] [IsDirectedOrder ι]
    (hunion : ∀ a : A, ∃ i, a ∈ W i) (n : ℕ) (x : cohomology A n) :
    ∃ (i : ι) (y : cohomology (A.subrepresentation (W i) (hstable i)) n),
      (cohomologyMap (Rep.subtype A (W i) (hstable i)) n).hom y = x := by sorry
