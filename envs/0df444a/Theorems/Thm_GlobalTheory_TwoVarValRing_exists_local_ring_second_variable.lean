-- Prove2me | Theorems.Thm_GlobalTheory_TwoVarValRing_exists_local_ring_second_variable
-- name    : GlobalTheory.TwoVarValRing.exists_local_ring_second_variable
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:16:19.724082+00:00
-- url     : https://prove2.me/theorems/c937fdec-0ecd-401e-944c-7bf9bb03aa55
-- title:
--   Two Var Val Ring: exists local ring second variable
-- statement:
--   The Two Var Val Ring construction uses the exists local ring second variable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLocalRingSecondVariable.lean#L100-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLocalRingSecondVariable.lean#L100-L134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLocalRingSecondVariable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TwoVarValRing

theorem GlobalTheory.TwoVarValRing.exists_local_ring_second_variable : ∀ (k : Type) [Field k] (σ₀ σ₁ : FractionRing (PowerSeries k) →ₐ[k] FractionRing (MvPowerSeries (Fin 2) k)), (∀ x : PowerSeries k, σ₀ (algebraMap _ _ x) = algebraMap (MvPowerSeries (Fin 2) k) _ (x.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k))) → (∀ x : PowerSeries k, σ₁ (algebraMap _ _ x) = algebraMap (MvPowerSeries (Fin 2) k) _ (x.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k))) → ∃ L : Subalgebra k (FractionRing (MvPowerSeries (Fin 2) k)), IsLocalRing L ∧ (∀ (x : FractionRing (MvPowerSeries (Fin 2) k)) (u v : MvPowerSeries (Fin 2) k), ¬ MvPowerSeries.X 1 ∣ v → x * algebraMap (MvPowerSeries (Fin 2) k) _ v = algebraMap (MvPowerSeries (Fin 2) k) _ u → x ∈ L) ∧ (∀ x, σ₀ x ∈ L) ∧ ∀ x, σ₁ x ∈ L → x ∈ Set.range (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) := by sorry
