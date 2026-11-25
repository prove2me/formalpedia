-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_euclidNorm_vecMul_unitary
-- name    : GroundTheory.Automorphic.Reduction.euclidNorm_vecMul_unitary
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:57:41.82242+00:00
-- url     : https://prove2.me/theorems/33ea74a1-e96b-5ab1-acf3-385ad7c05026
-- title:
--   Reduction: euclid Norm vec Mul unitary
-- statement:
--   The Reduction construction uses the euclid Norm vec Mul unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L32-L34

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

theorem GroundTheory.Automorphic.Reduction.euclidNorm_vecMul_unitary {U : Matrix (Fin n) (Fin n) 𝕜} (hU : U ∈ unitaryGroup (Fin n) 𝕜)
    (z : Fin n → 𝕜) : euclidNorm (z ᵥ* U) = euclidNorm z := by sorry
