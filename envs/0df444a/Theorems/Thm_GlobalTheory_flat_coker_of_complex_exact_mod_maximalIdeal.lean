-- Prove2me | Theorems.Thm_GlobalTheory_flat_coker_of_complex_exact_mod_maximalIdeal
-- name    : GlobalTheory.flat_coker_of_complex_exact_mod_maximalIdeal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:52:10.99757+00:00
-- url     : https://prove2.me/theorems/408c7d8a-0548-43ee-a8bc-6118e9ccf81f
-- title:
--   Global Theory: flat coker of complex exact mod maximal Ideal
-- statement:
--   The Global Theory construction uses the flat coker of complex exact mod maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FlatCokerOfComplexExactModMaximalIdeal.lean#L8-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FlatCokerOfComplexExactModMaximalIdeal.lean#L8-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatCokerOfInjectiveModMaximalIdealStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatCokerOfComplexExactModMaximalIdeal
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

theorem GlobalTheory.flat_coker_of_complex_exact_mod_maximalIdeal : ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)] (D : ℕ → Type) [∀ i, AddCommGroup (D i)] [∀ i, Module A (D i)] [∀ i, Module.Finite A (D i)] [∀ i, Module V (D i)] [∀ i, IsScalarTower V A (D i)] [∀ i, Module.Flat V (D i)] (d : ∀ i, D (i + 1) →ₗ[A] D i), (∀ i x, d i (d (i + 1) x) = 0) → (∃ n, ∀ i, n < i → Subsingleton (D i)) → (∀ i (x : D (i + 1)), d i x ∈ (((IsLocalRing.maximalIdeal V).map (algebraMap V A)) • ⊤ : Submodule A (D i)) → x ∈ LinearMap.range (d (i + 1)) ⊔ (((IsLocalRing.maximalIdeal V).map (algebraMap V A)) • ⊤ : Submodule A (D (i + 1)))) → Module.Flat V (D 0 ⧸ LinearMap.range (d 0)) := by sorry
