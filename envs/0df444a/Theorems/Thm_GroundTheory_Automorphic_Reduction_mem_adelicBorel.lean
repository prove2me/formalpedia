-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_mem_adelicBorel
-- name    : GroundTheory.Automorphic.Reduction.mem_adelicBorel
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:50:00.738413+00:00
-- url     : https://prove2.me/theorems/d6e3ced6-36af-517e-934e-9e497d31e31c
-- title:
--   Reduction: mem adelic Borel
-- statement:
--   The Reduction construction uses the mem adelic Borel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L236-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L236-L238

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

theorem GroundTheory.Automorphic.Reduction.mem_adelicBorel {b : AdelicGLn.AdelicGL K n} :
    b ∈ adelicBorel ↔ (b : Matrix (Fin n) (Fin n) 𝔸[K]).IsUpperTriangular := by sorry
