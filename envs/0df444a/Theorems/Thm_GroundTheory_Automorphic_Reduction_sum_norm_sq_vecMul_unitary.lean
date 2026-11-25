-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_sum_norm_sq_vecMul_unitary
-- name    : GroundTheory.Automorphic.Reduction.sum_norm_sq_vecMul_unitary
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:24.53521+00:00
-- url     : https://prove2.me/theorems/eb3061f3-3f51-4c78-9e50-5548ebc54b93
-- title:
--   Reduction: sum norm sq vec Mul unitary
-- statement:
--   The Reduction construction uses the sum norm sq vec Mul unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L20-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L20-L30

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
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

theorem GroundTheory.Automorphic.Reduction.sum_norm_sq_vecMul_unitary {U : Matrix (Fin n) (Fin n) 𝕜} (hU : U ∈ unitaryGroup (Fin n) 𝕜)
    (z : Fin n → 𝕜) : ∑ j, ‖(z ᵥ* U) j‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by sorry
