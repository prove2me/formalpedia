-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_diagonal_blockOneHom
-- name    : GroundTheory.Automorphic.Reduction.diagonal_blockOneHom
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:07:55.222091+00:00
-- url     : https://prove2.me/theorems/3860b522-be53-51b6-b910-c5f0e34cdbea
-- title:
--   Reduction: diagonal block One Hom
-- statement:
--   The Reduction construction uses the diagonal block One Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L99-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L99-L102

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

theorem GroundTheory.Automorphic.Reduction.diagonal_blockOneHom {m : ℕ} (γ : GL (Fin m) K) :
    AdelicGLn.diagonal K (m + 1) (blockOneHom γ) = blockOneHom (AdelicGLn.diagonal K m γ) := by sorry
