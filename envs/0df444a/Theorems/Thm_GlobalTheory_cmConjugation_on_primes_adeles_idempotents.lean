-- Prove2me | Theorems.Thm_GlobalTheory_cmConjugation_on_primes_adeles_idempotents
-- name    : GlobalTheory.cmConjugation_on_primes_adeles_idempotents
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:03:47.258574+00:00
-- url     : https://prove2.me/theorems/5bdd8b6c-5dcc-435f-9616-3e40c71be165
-- title:
--   Global Theory: cm Conjugation on primes adeles idempotents
-- statement:
--   The Global Theory construction uses the cm Conjugation on primes adeles idempotents property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/CmConjugationOnPrimesProperties.lean#L57-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/CmConjugationOnPrimesProperties.lean#L57-L97

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_ThmBInHecke
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPrimeInvolutionOfRingInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CmConjugationOnPrimesProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors
open GlobalTheory

theorem GlobalTheory.cmConjugation_on_primes_adeles_idempotents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ c : HeightOneSpectrum (𝓞 E) ≃ HeightOneSpectrum (𝓞 E), (∀ P, c (c P) = P) ∧ (∀ P, normP (c P) = normP P) ∧ (∀ P (x y : 𝓞 E), (y : E) = σ x → (y ∈ (c P).asIdeal ↔ x ∈ P.asIdeal) ∧ (y ∈ (c P).asIdeal ^ 2 ↔ x ∈ P.asIdeal ^ 2)) ∧ (∀ P Q : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = Q.under (𝓞 F) ↔ Q = P ∨ Q = c P) ∧ (∀ y, cA σ (cA σ y) = y) ∧ (∀ y : AE F E, finPart F E (cA σ y) ∈ intAE F E ↔ finPart F E y ∈ intAE F E) ∧ ∀ P e f, IsPrimeIdem σ P e f → IsPrimeIdem σ (c P) (cA σ e) f := by sorry
