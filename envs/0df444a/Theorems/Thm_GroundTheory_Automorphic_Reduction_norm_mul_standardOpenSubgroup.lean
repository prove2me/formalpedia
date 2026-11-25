-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_mul_standardOpenSubgroup
-- name    : GroundTheory.Automorphic.Reduction.norm_mul_standardOpenSubgroup
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:06:59.339346+00:00
-- url     : https://prove2.me/theorems/bbff4f7c-324e-473a-8830-25dfa8fcd171
-- title:
--   Reduction: norm mul standard Open Subgroup
-- statement:
--   The Reduction construction uses the norm mul standard Open Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionDirichlet.lean#L227-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionDirichlet.lean#L227-L232

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

theorem GroundTheory.Automorphic.Reduction.norm_mul_standardOpenSubgroup (s : IdeleGroup K) {u : IdeleGroup K}
    (hu : u ∈ standardOpenSubgroup K) (v : HeightOneSpectrum (𝓞 K)) :
    ‖((s * u : IdeleGroup K) : 𝔸[K]).2 v‖ = ‖(s : 𝔸[K]).2 v‖ := by sorry
