-- Prove2me | Theorems.Thm_GlobalTheory_SymAlg_mapOver_mem_homog
-- name    : GlobalTheory.SymAlg.mapOver_mem_homog
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:25:10.198622+00:00
-- url     : https://prove2.me/theorems/1cbba1fa-1c5f-4bc4-9d56-2343cf15652f
-- title:
--   Sym Alg: map Over mem homog
-- statement:
--   The Sym Alg construction uses the map Over mem homog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemHomogIffIsHomogeneous.lean#L199-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemHomogIffIsHomogeneous.lean#L199-L209

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open scoped DirectSum
open GlobalTheory
open GlobalTheory.SymAlg
variable {R : Type*} [CommRing R] {M M' M'' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
variable {S : Type*} [CommRing S] [Algebra R S] {W : Type*} [AddCommGroup W] [Module R W]
  [Module S W] [IsScalarTower R S W]

theorem GlobalTheory.SymAlg.mapOver_mem_homog (j : M →ₗ[R] W) {d : ℕ} {x : SymmetricAlgebra R M}
    (hx : x ∈ homog R M d) : mapOver S j x ∈ homog S W d := by sorry
