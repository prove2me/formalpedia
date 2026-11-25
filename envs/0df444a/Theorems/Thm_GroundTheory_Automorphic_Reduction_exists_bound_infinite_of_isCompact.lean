-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_bound_infinite_of_isCompact
-- name    : GroundTheory.Automorphic.Reduction.exists_bound_infinite_of_isCompact
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:03:33.012234+00:00
-- url     : https://prove2.me/theorems/36555388-2831-5224-9e1c-52d7472c5605
-- title:
--   Reduction: exists bound infinite of is Compact
-- statement:
--   The Reduction construction uses the exists bound infinite of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionDirichlet.lean#L210-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionDirichlet.lean#L210-L218

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionDirichlet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Automorphic.Reduction.exists_bound_infinite_of_isCompact {S : Set (IdeleGroup K)} (hS : IsCompact S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ S, ∀ w : InfinitePlace K, ‖(s : 𝔸[K]).1 w‖ ≤ M := by sorry
