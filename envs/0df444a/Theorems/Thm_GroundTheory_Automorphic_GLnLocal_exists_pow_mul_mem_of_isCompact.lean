-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_pow_mul_mem_of_isCompact
-- name    : GroundTheory.Automorphic.GLnLocal.exists_pow_mul_mem_of_isCompact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:28.874948+00:00
-- url     : https://prove2.me/theorems/adec2085-1ec2-46da-bb4a-e920746049a5
-- title:
--   GLn Local: exists pow mul mem of is Compact
-- statement:
--   The GLn Local construction uses the exists pow mul mem of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L353-L376
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L353-L376

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Topology Filter Set
open scoped Pointwise Matrix
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.GLnLocal.exists_pow_mul_mem_of_isCompact {S : Set (GL (Fin n) F)} (hS : IsCompact S) :
    ∃ m : ℕ, ∀ g ∈ S, ∀ i j, (uniformizer F : F) ^ m * g i j ∈ 𝒪[F] := by sorry
