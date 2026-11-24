-- Prove2me | Theorems.Thm_GlobalTheory_splitting_absence_spreads
-- name    : GlobalTheory.splitting_absence_spreads
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:21:51.795027+00:00
-- url     : https://prove2.me/theorems/fb2976a1-0c77-4a88-b87c-24ba8742c863
-- title:
--   Global Theory: splitting absence spreads
-- statement:
--   The Global Theory construction uses the splitting absence spreads property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplittingAbsenceSpreads.lean#L162-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplittingAbsenceSpreads.lean#L162-L169

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NoCommonZeroSpreadsConstructibleNbhdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplittingAbsenceSpreads
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem GlobalTheory.splitting_absence_spreads : ∀ (A : Type) [CommRing A] (σ : Type) [Finite σ] (f g : MvPolynomial σ A) (D : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = MvPolynomial.map φ f ∧ ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P (MvPolynomial.map φ g) ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q (MvPolynomial.map φ g) ≠ 0) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → ¬ (∃ u v : MvPolynomial σ k, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = MvPolynomial.map ψ f ∧ ∃ P Q : σ → k, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P (MvPolynomial.map ψ g) ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0) := by sorry
