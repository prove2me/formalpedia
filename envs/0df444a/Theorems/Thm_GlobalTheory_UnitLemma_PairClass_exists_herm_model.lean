-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_PairClass_exists_herm_model
-- name    : GlobalTheory.UnitLemma.PairClass.exists_herm_model
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:29:25.993499+00:00
-- url     : https://prove2.me/theorems/80a36cae-9939-4c7a-97e9-609e97244617
-- title:
--   Pair Class: exists herm model
-- statement:
--   The Pair Class construction uses the exists herm model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAevalEqOfSeparable.lean#L142-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAevalEqOfSeparable.lean#L142-L224

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ExistsNeZeroAevalEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfSeparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.PairClass

theorem GlobalTheory.UnitLemma.PairClass.exists_herm_model : ∀ (K : UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V] [Module.Finite K.E V] (h : V → V → K.E), (∀ x y z, h (x + y) z = h x z + h y z) → (∀ (c : K.E) x z, h (c • x) z = c * h x z) → (∀ x y, h y x = K.c (h x y)) → (∀ y, (∀ z, h y z = 0) → y = 0) → ∀ (B : InvAlg K) (g : V →ₗ[K.E] V), B.P.Separable → g.charpoly = B.P → ((B.g * B.σ B.g = 1 ∧ ∀ y z, h (g y) (g z) = h y z) ∨ (B.σ B.g = B.g ∧ ∀ y z, h (g y) z = h y (g z))) → ∃ (x : B.Aˣ) (e : B.A ≃ₗ[K.E] V), B.σ (x : B.A) = x ∧ (∀ y, e (B.g * y) = g (e y)) ∧ ∀ y z, h (e y) (e z) = B.herm x y z := by sorry
