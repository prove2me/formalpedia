-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_adelicNorm_vecMul_maxCompact
-- name    : GroundTheory.Automorphic.Reduction.adelicNorm_vecMul_maxCompact
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:57:35.499921+00:00
-- url     : https://prove2.me/theorems/ce690913-c649-564d-9725-3c8eb5c1df22
-- title:
--   Reduction: adelic Norm vec Mul max Compact
-- statement:
--   The Reduction construction uses the adelic Norm vec Mul max Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L311-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L311-L319

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

theorem GroundTheory.Automorphic.Reduction.adelicNorm_vecMul_maxCompact (y : Fin n → 𝔸[K]) {k : AdelicGLn.AdelicGL K n}
    (hk : k ∈ maxCompact) :
    adelicNorm (y ᵥ* (k : Matrix (Fin n) (Fin n) 𝔸[K])) = adelicNorm y := by sorry
