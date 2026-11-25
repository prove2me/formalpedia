-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_le_one_of_mem_integralFiniteAdeles
-- name    : GroundTheory.Automorphic.Reduction.norm_le_one_of_mem_integralFiniteAdeles
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:06:49.515878+00:00
-- url     : https://prove2.me/theorems/e5457cb3-649d-40e8-ab6a-94c50263368a
-- title:
--   Reduction: norm le one of mem integral Finite Adeles
-- statement:
--   The Reduction construction uses the norm le one of mem integral Finite Adeles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionDirichlet.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionDirichlet.lean#L55-L58

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

theorem GroundTheory.Automorphic.Reduction.norm_le_one_of_mem_integralFiniteAdeles {a : FiniteAdeleRing (𝓞 K) K}
    (ha : a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    ‖a v‖ ≤ 1 := by sorry
