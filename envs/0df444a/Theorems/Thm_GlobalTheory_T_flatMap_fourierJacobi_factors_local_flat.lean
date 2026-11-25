-- Prove2me | Theorems.Thm_GlobalTheory_T_flatMap_fourierJacobi_factors_local_flat
-- name    : GlobalTheory.T.flatMap_fourierJacobi_factors_local_flat
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:39:45.02313+00:00
-- url     : https://prove2.me/theorems/3cddcad9-baae-5c42-8512-e7f37b69cc47
-- title:
--   T: flat Map fourier Jacobi factors local flat
-- statement:
--   The T construction uses the flat Map fourier Jacobi factors local flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapFourierJacobiFactorsLocalFlatStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapFourierJacobiFactorsLocalFlatStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapFourierJacobiFactorsLocalFlat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapFourierJacobiFactorsLocalFlatStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.flatMap_fourierJacobi_factors_local_flat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val < ρ ∧ ¬ Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l, r = Sum.inr l ∧ ρ ≤ l.val ∧ ∀ i, q = Sum.inr i → i.val = ρ) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), Free (ρ + 1) (r, q) → (∀ i, q = Sum.inr i → ρ ≤ i.val) → ∀ (a : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single r q a)) → L Φ' = (ψ (ch (Matrix.single r q a)) : ℂ) • L Φ) → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → (∀ l l' : Fin c, l.val < ρ → ρ ≤ l'.val → u.val l l' = 0) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∃ L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ.1 → L Φ = L₀ Ψ := by sorry
