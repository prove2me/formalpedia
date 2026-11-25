-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_blockOneHom_mem_maxCompact
-- name    : GroundTheory.Automorphic.Reduction.blockOneHom_mem_maxCompact
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:57:22.130975+00:00
-- url     : https://prove2.me/theorems/cab518cb-a0b7-4835-8d0c-287c1a8f13e3
-- title:
--   Reduction: block One Hom mem max Compact
-- statement:
--   The Reduction construction uses the block One Hom mem max Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L147-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L147-L150

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionFinite
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionBlock
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionDirichlet
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionCore
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
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Automorphic.Reduction.blockOneHom_mem_maxCompact {m : ℕ} {k : AdelicGLn.AdelicGL K m} (hk : k ∈ maxCompact) :
    blockOneHom k ∈ maxCompact (n := m + 1) := by sorry
