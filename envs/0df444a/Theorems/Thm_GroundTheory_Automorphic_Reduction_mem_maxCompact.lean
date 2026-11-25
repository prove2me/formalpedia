-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_mem_maxCompact
-- name    : GroundTheory.Automorphic.Reduction.mem_maxCompact
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:12:58.618977+00:00
-- url     : https://prove2.me/theorems/115fdecf-32fc-5d2f-a5f4-2ff90819e7bb
-- title:
--   Reduction: mem max Compact
-- statement:
--   The Reduction construction uses the mem max Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L203-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L203-L206

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

theorem GroundTheory.Automorphic.Reduction.mem_maxCompact {k : AdelicGLn.AdelicGL K n} :
    k ∈ maxCompact ↔ (∀ w, infAt w k ∈ archCompact w) ∧
      ∀ v, finAt v k ∈ GLnLocal.integralGL (v.adicCompletion K) n := by sorry
