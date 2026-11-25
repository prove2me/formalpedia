-- Prove2me | Theorems.Thm_GlobalTheory_SymAlg_mapOver_injective
-- name    : GlobalTheory.SymAlg.mapOver_injective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:24:47.26416+00:00
-- url     : https://prove2.me/theorems/5849cd9c-c5a1-5f6d-8c99-915239c606aa
-- title:
--   Sym Alg: map Over injective
-- statement:
--   The Sym Alg construction uses the map Over injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemHomogIffIsHomogeneous.lean#L211-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemHomogIffIsHomogeneous.lean#L211-L219

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

theorem GlobalTheory.SymAlg.mapOver_injective [Module.Projective R M] {j : M →ₗ[R] W} (h : IsBaseChange S j)
    (hS : Function.Injective (algebraMap R S)) : Function.Injective (mapOver S j) := by sorry
