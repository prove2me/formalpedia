-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_apply_le_norm_homeomorphMixedSpace
-- name    : GroundTheory.Automorphic.Reduction.norm_apply_le_norm_homeomorphMixedSpace
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:04:37.570594+00:00
-- url     : https://prove2.me/theorems/5fefba1f-1634-4b66-98ff-a713c8cc44d7
-- title:
--   Reduction: norm apply le norm homeomorph Mixed Space
-- statement:
--   The Reduction construction uses the norm apply le norm homeomorph Mixed Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionDirichlet.lean#L23-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionDirichlet.lean#L23-L43

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
open scoped Classical

theorem GroundTheory.Automorphic.Reduction.norm_apply_le_norm_homeomorphMixedSpace (x : InfiniteAdeleRing K) (w : InfinitePlace K) :
    ‖x w‖ ≤ ‖GroundTheory.Global.homeomorphMixedSpace K x‖ := by sorry
