-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_adelicNorm_vecMul_le
-- name    : GroundTheory.Automorphic.Reduction.exists_adelicNorm_vecMul_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:06:11.949139+00:00
-- url     : https://prove2.me/theorems/ddd90b88-c12c-483c-b2da-a0742bcca64f
-- title:
--   Reduction: exists adelic Norm vec Mul le
-- statement:
--   The Reduction construction uses the exists adelic Norm vec Mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionDirichlet.lean#L335-L497
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionDirichlet.lean#L335-L497

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionDirichlet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Automorphic.Reduction.exists_adelicNorm_vecMul_le : ∃ C : ℝ, 0 < C ∧ ∀ (α δ : IdeleGroup K) (u : 𝔸[K]),
    ∃ x : Fin 2 → K, x ≠ 0 ∧ adelicNorm (ratVec x ᵥ* !![(α : 𝔸[K]), u; 0, (δ : 𝔸[K])]) ≤
      C * Real.sqrt (ideleModule K (α * δ) : ℝ) := by sorry
