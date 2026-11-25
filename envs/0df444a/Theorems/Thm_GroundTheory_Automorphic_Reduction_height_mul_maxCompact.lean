-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_height_mul_maxCompact
-- name    : GroundTheory.Automorphic.Reduction.height_mul_maxCompact
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:57:50.923362+00:00
-- url     : https://prove2.me/theorems/04dd45b0-e846-5df8-96a5-9aa244c40d4d
-- title:
--   Reduction: height mul max Compact
-- statement:
--   The Reduction construction uses the height mul max Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L321-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L321-L323

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

theorem GroundTheory.Automorphic.Reduction.height_mul_maxCompact (g : AdelicGLn.AdelicGL K n) {k : AdelicGLn.AdelicGL K n}
    (hk : k ∈ maxCompact) (x : Fin n → K) : height (g * k) x = height g x := by sorry
