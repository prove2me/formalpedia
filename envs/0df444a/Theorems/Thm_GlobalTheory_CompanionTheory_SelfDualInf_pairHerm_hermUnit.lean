-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_pairHerm_hermUnit
-- name    : GlobalTheory.CompanionTheory.SelfDualInf.pairHerm_hermUnit
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:38:06.308336+00:00
-- url     : https://prove2.me/theorems/f3792f20-9ae8-4526-9096-398fa8111743
-- title:
--   Self Dual Inf: pair Herm herm Unit
-- statement:
--   The Self Dual Inf construction uses the pair Herm herm Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/HasCoordOfFiniteDimensional.lean#L294-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/HasCoordOfFiniteDimensional.lean#L294-L309

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_HasCoordOfFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SelfDualInf
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)

theorem GlobalTheory.CompanionTheory.SelfDualInf.pairHerm_hermUnit [CharZero F] (hσ : ∀ x, σ (σ x) = x) (n : ℕ) (S : HermR R σ n)
    (a b : Fin n) (u : R ⊗[F] E) :
    pairHerm R σ n S (hermUnit R σ hσ n a b u) = Algebra.trace R (R ⊗[F] E)
      ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a b * u) := by sorry
