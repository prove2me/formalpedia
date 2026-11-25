-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_unitriangular_mul_mem
-- name    : GroundTheory.Automorphic.Reduction.exists_unitriangular_mul_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:50:02.657073+00:00
-- url     : https://prove2.me/theorems/4245397d-487a-43e7-aa92-24191368783a
-- title:
--   Reduction: exists unitriangular mul mem
-- statement:
--   The Reduction construction uses the exists unitriangular mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L109-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L109-L141

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionCore
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionSiegel
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

theorem GroundTheory.Automorphic.Reduction.exists_unitriangular_mul_mem {D : Set 𝔸[K]}
    (hD : ∀ x : 𝔸[K], ∃ k : K, x + algebraMap K 𝔸[K] k ∈ D) :
    ∀ (m : ℕ) (u : Matrix (Fin m) (Fin m) 𝔸[K]), IsUnitriangular u →
      ∃ ν : Matrix (Fin m) (Fin m) K, IsUnitriangular ν ∧
        ∀ i j, i < j → (ν.map (algebraMap K 𝔸[K]) * u) i j ∈ D := by sorry
