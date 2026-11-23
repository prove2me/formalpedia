-- Prove2me | Theorems.Thm_GlobalTheory_flat_coker_of_injective_mod_maximalIdeal
-- name    : GlobalTheory.flat_coker_of_injective_mod_maximalIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:36.693255+00:00
-- url     : https://prove2.me/theorems/4eaaa1aa-beb2-425f-ad37-cc18ef32803d
-- title:
--   Global Theory: flat coker of injective mod maximal Ideal
-- statement:
--   The Global Theory construction uses the flat coker of injective mod maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FlatCokerOfInjectiveModMaximalIdeal.lean#L185-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FlatCokerOfInjectiveModMaximalIdeal.lean#L185-L249

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatCokerOfInjectiveModMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct
open GlobalTheory
open CategoryTheory CategoryTheory.Limits TensorProduct

theorem GlobalTheory.flat_coker_of_injective_mod_maximalIdeal : ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)] (M N : Type) [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup N] [Module A N] [Module V N] [IsScalarTower V A N] [Module.Flat V N] (u : M →ₗ[A] N), (∀ x : M, u x ∈ (((IsLocalRing.maximalIdeal V).map (algebraMap V A)) • ⊤ : Submodule A N) → x ∈ (((IsLocalRing.maximalIdeal V).map (algebraMap V A)) • ⊤ : Submodule A M)) → Module.Flat V (N ⧸ LinearMap.range u) := by sorry
