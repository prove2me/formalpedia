-- Prove2me | Theorems.Thm_GlobalTheory_preirreducibleSpace_fibre_standardEtale_spreads
-- name    : GlobalTheory.preirreducibleSpace_fibre_standardEtale_spreads
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:15:52.211959+00:00
-- url     : https://prove2.me/theorems/74e25660-c4bb-46ec-96d2-3d7e5ecfca7e
-- title:
--   Global Theory: preirreducible Space fibre standard Etale spreads
-- statement:
--   The Global Theory construction uses the preirreducible Space fibre standard Etale spreads property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleFibreStandardEtaleSpreads.lean#L28-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleFibreStandardEtaleSpreads.lean#L28-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HypersurfacePartGeometricIrreducibleSpreadsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StandardEtaleMvPolynomialHypersurfaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceFibreHypersurfaceSpectrumIffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleFibreStandardEtaleSpreads
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
open GlobalTheory

theorem GlobalTheory.preirreducibleSpace_fibre_standardEtale_spreads :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B], Algebra.IsStandardEtale (MvPolynomial (Fin n) A) B → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω], PreirreducibleSpace (PrimeSpectrum (Ω ⊗[A] B)) → ∃ (a : A) (I : Finset A), algebraMap A Ω a ≠ 0 ∧ (∀ c ∈ I, algebraMap A Ω c = 0) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra A k], algebraMap A k a ≠ 0 → (∀ c ∈ I, algebraMap A k c = 0) → PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) := by sorry
