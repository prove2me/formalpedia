-- Prove2me | Theorems.Thm_GlobalTheory_exists_noetherian_subring_homogeneous_matrix_flat_charts
-- name    : GlobalTheory.exists_noetherian_subring_homogeneous_matrix_flat_charts
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:54:45.831156+00:00
-- url     : https://prove2.me/theorems/d56f9af1-875c-415a-a273-dbb7640c2b5d
-- title:
--   Global Theory: exists noetherian subring homogeneous matrix flat charts
-- statement:
--   The Global Theory construction uses the exists noetherian subring homogeneous matrix flat charts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsNoetherianSubringHomogeneousMatrixFlatChar.lean#L186-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsNoetherianSubringHomogeneousMatrixFlatChar.lean#L186-L287

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsWitnessesOfFormallySmoothQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FlatQuotSMulTopCokerOfMatrixWitnesses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsNoetherianSubringHomogeneousMatrixFlatChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct

theorem GlobalTheory.exists_noetherian_subring_homogeneous_matrix_flat_charts :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (a b : ℕ) (d : Fin a → ℤ) (e : Fin b → ℤ) (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)), (∀ l j, Φ l j ∈ _root_.GlobalTheory.polyGrading ι R (e j - d l)) → (∀ i : ι, ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (π : MvPolynomial ι R →ₐ[R] B) (P : Type) (_ : AddCommGroup P) (_ : Module B P) (ε : (Fin a → MvPolynomial ι R) →ₛₗ[(π : MvPolynomial ι R →+* B)] P), Algebra.Smooth R B ∧ Module.Projective B P ∧ Function.Surjective π ∧ π (X i) = 1 ∧ Function.Surjective ε ∧ ∀ y, ε y = 0 ↔ ∃ w w', y = Φ.mulVec w + (X i - 1 : MvPolynomial ι R) • w') → ∃ (R₀ : Subring R) (Φ₀ : Matrix (Fin a) (Fin b) (MvPolynomial ι R₀)), IsNoetherianRing R₀ ∧ Φ₀.map (MvPolynomial.map R₀.subtype) = Φ ∧ (∀ l j, Φ₀ l j ∈ _root_.GlobalTheory.polyGrading ι R₀ (e j - d l)) ∧ ∀ i : ι, Module.Flat R₀ (QuotSMulTop (X i - 1 : MvPolynomial ι R₀) ((Fin a → MvPolynomial ι R₀) ⧸ LinearMap.range Φ₀.mulVecLin)) := by sorry
