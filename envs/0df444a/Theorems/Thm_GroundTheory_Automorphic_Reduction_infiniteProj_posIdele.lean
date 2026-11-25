-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_infiniteProj_posIdele
-- name    : GroundTheory.Automorphic.Reduction.infiniteProj_posIdele
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:56:24.135377+00:00
-- url     : https://prove2.me/theorems/f7d37c8f-c2a8-42f3-bddb-ea98f7fbd3d1
-- title:
--   Reduction: infinite Proj pos Idele
-- statement:
--   The Reduction construction uses the infinite Proj pos Idele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionDirichlet.lean#L257-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionDirichlet.lean#L257-L264

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

theorem GroundTheory.Automorphic.Reduction.infiniteProj_posIdele (ρ : ℝ) (hρ : 0 < ρ) (w : InfinitePlace K) :
    infiniteProj w (posIdele ρ hρ) = posRealToUnits w ⟨ρ ^ w.mult, pow_pos hρ _⟩ := by sorry
