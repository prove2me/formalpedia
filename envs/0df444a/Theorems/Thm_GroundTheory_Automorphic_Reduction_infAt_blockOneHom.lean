-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_infAt_blockOneHom
-- name    : GroundTheory.Automorphic.Reduction.infAt_blockOneHom
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:08:26.231133+00:00
-- url     : https://prove2.me/theorems/361c1864-4318-59d0-8e9c-c8b1de5bd5d3
-- title:
--   Reduction: inf At block One Hom
-- statement:
--   The Reduction construction uses the inf At block One Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L104-L107

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

theorem GroundTheory.Automorphic.Reduction.infAt_blockOneHom {m : ℕ} (w : InfinitePlace K) (k : AdelicGLn.AdelicGL K m) :
    infAt w (blockOneHom k) = blockOneHom (infAt w k) := by sorry
