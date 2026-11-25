-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_finAt_blockOneHom
-- name    : GroundTheory.Automorphic.Reduction.finAt_blockOneHom
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:11:45.427312+00:00
-- url     : https://prove2.me/theorems/b14b8985-2f9c-4f96-9614-e631402b24bf
-- title:
--   Reduction: fin At block One Hom
-- statement:
--   The Reduction construction uses the fin At block One Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L109-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L109-L112

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

theorem GroundTheory.Automorphic.Reduction.finAt_blockOneHom {m : ℕ} (v : HeightOneSpectrum (𝓞 K)) (k : AdelicGLn.AdelicGL K m) :
    finAt v (blockOneHom k) = blockOneHom (finAt v k) := by sorry
