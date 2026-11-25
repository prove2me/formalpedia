-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_mem_standardLattice
-- name    : GroundTheory.Automorphic.GLnLocal.mem_standardLattice
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:29:34.853493+00:00
-- url     : https://prove2.me/theorems/b1ceadb6-c45d-4adc-b4d3-46b2e47f3d5d
-- title:
--   GLn Local: mem standard Lattice
-- statement:
--   The GLn Local construction uses the mem standard Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L67-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L67-L68

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

theorem GroundTheory.Automorphic.GLnLocal.mem_standardLattice {v : Fin n → F} : v ∈ standardLattice F n ↔ ∀ i, v i ∈ 𝒪[F] := by sorry
