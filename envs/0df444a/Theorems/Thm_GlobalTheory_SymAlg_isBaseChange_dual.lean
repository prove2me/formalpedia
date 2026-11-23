-- Prove2me | Theorems.Thm_GlobalTheory_SymAlg_isBaseChange_dual
-- name    : GlobalTheory.SymAlg.isBaseChange_dual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:37.26836+00:00
-- url     : https://prove2.me/theorems/c7898951-3998-433a-802d-f911e4b8b751
-- title:
--   Sym Alg: is Base Change dual
-- statement:
--   The Sym Alg construction uses the is Base Change dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemHomogIffIsHomogeneous.lean#L173-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemHomogIffIsHomogeneous.lean#L173-L197

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

theorem GlobalTheory.SymAlg.isBaseChange_dual [Module.Finite R M] [Module.Projective R M] {j : M →ₗ[R] W}
    (h : IsBaseChange S j) : IsBaseChange S h.toDual := by sorry
