-- Prove2me | Theorems.Thm_GlobalTheory_SymAlg_baseChangeEquiv_tmul
-- name    : GlobalTheory.SymAlg.baseChangeEquiv_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:54.310856+00:00
-- url     : https://prove2.me/theorems/5615a31b-ba83-4cb4-8fda-f08a48877865
-- title:
--   Sym Alg: base Change Equiv tmul
-- statement:
--   The Sym Alg construction uses the base Change Equiv tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemHomogIffIsHomogeneous.lean#L169-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemHomogIffIsHomogeneous.lean#L169-L171

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

theorem GlobalTheory.SymAlg.baseChangeEquiv_tmul {j : M →ₗ[R] W} (h : IsBaseChange S j) (s : S)
    (x : SymmetricAlgebra R M) : baseChangeEquiv h (s ⊗ₜ x) = s • mapOver S j x := by sorry
