-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_adelicBorel_mul_maxCompact
-- name    : GroundTheory.Automorphic.Reduction.exists_adelicBorel_mul_maxCompact
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:59:05.525683+00:00
-- url     : https://prove2.me/theorems/7f90fb3a-3232-4cf9-8ad0-ffd5609c6809
-- title:
--   Reduction: exists adelic Borel mul max Compact
-- statement:
--   The Reduction construction uses the exists adelic Borel mul max Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L257-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L257-L309

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

theorem GroundTheory.Automorphic.Reduction.exists_adelicBorel_mul_maxCompact (g : AdelicGLn.AdelicGL K n) :
    ∃ b ∈ adelicBorel, ∃ k ∈ maxCompact, g = b * k := by sorry
