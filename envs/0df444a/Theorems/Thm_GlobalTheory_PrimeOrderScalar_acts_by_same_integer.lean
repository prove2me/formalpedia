-- Prove2me | Theorems.Thm_GlobalTheory_PrimeOrderScalar_acts_by_same_integer
-- name    : GlobalTheory.PrimeOrderScalar.acts_by_same_integer
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:30:54.630937+00:00
-- url     : https://prove2.me/theorems/e7d2a3aa-2def-4137-928e-80873d7ebcdb
-- title:
--   Prime Order Scalar: acts by same integer
-- statement:
--   The Prime Order Scalar construction uses the acts by same integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ActsBySameInteger.lean#L180-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ActsBySameInteger.lean#L180-L253

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ActsBySameInteger
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open GlobalTheory GlobalTheory.PrimeOrderScalar
open scoped TensorProduct

theorem GlobalTheory.PrimeOrderScalar.acts_by_same_integer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)), (∀ x, σ (σ x) = x) → (∀ x, σ x = x → x ∈ (algebraMap F E).range) → ∀ (T : ℕ), T.Prime → (T : 𝓞 F) ∈ w.asIdeal → ∀ (p : 𝓞 E), (∀ d : 𝓞 F, algebraMap F E (d : F) = (p : E) + σ (p : E) → d ∉ w.asIdeal) → ∀ (A B : Type) [AddCommGroup A] [Module (intV E w) A] [AddCommGroup B] [Module (intV E w) B], Nat.card A = T → Nat.card B = T → (∀ a : intV E w, (a : TensorProduct F E (w.adicCompletion F)) = inclE (F := F) (w.adicCompletion F) (p : E) → ∀ m : A, a • m = 0) → (∀ a : intV E w, (a : TensorProduct F E (w.adicCompletion F)) = inclE (F := F) (w.adicCompletion F) (p : E) → ∀ m : B, a • m = 0) → ∀ s : intV E w, ∃ k : ℤ, (∀ m : A, s • m = k • m) ∧ ∀ m : B, s • m = k • m := by sorry
