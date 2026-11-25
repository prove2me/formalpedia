-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_finite_setOf_algebraMap_mem
-- name    : GroundTheory.Automorphic.Reduction.finite_setOf_algebraMap_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:04:59.91875+00:00
-- url     : https://prove2.me/theorems/c0f230e2-b678-4a53-ac7a-eaa13d5b66fb
-- title:
--   Reduction: finite set Of algebra Map mem
-- statement:
--   The Reduction construction uses the finite set Of algebra Map mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L194-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L194-L202

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem GroundTheory.Automorphic.Reduction.finite_setOf_algebraMap_mem {D : Set 𝔸[K]} (hD : IsCompact D) :
    {k : K | algebraMap K 𝔸[K] k ∈ D}.Finite := by sorry
