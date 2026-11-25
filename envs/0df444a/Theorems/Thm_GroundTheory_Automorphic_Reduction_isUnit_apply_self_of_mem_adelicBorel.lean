-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_isUnit_apply_self_of_mem_adelicBorel
-- name    : GroundTheory.Automorphic.Reduction.isUnit_apply_self_of_mem_adelicBorel
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:50:12.32891+00:00
-- url     : https://prove2.me/theorems/5a81cda3-a934-5510-b0b6-f64a376b3b6b
-- title:
--   Reduction: is Unit apply self of mem adelic Borel
-- statement:
--   The Reduction construction uses the is Unit apply self of mem adelic Borel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L240-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L240-L246

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa
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
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] {n : ℕ}
variable [NumberField K]

theorem GroundTheory.Automorphic.Reduction.isUnit_apply_self_of_mem_adelicBorel {b : AdelicGLn.AdelicGL K n} (hb : b ∈ adelicBorel)
    (i : Fin n) : IsUnit ((b : Matrix (Fin n) (Fin n) 𝔸[K]) i i) := by sorry
