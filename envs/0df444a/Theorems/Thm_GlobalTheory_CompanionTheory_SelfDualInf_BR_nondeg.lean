-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_BR_nondeg
-- name    : GlobalTheory.CompanionTheory.SelfDualInf.BR_nondeg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:38:26.65281+00:00
-- url     : https://prove2.me/theorems/5bd80fd4-c7c3-4bc0-9a3b-2ff89a972419
-- title:
--   Self Dual Inf: BR nondeg
-- statement:
--   The Self Dual Inf construction uses the BR nondeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/HasCoordOfFiniteDimensional.lean#L241-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/HasCoordOfFiniteDimensional.lean#L241-L274

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

theorem GlobalTheory.CompanionTheory.SelfDualInf.BR_nondeg [Algebra.IsSeparable F E] (L : R →+ ℝ)
    (hL : ∀ t, (∀ r, L (r * t) = 0) → t = 0) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hdet : J.det ≠ 0) (X : Fin n → Fin M → R ⊗[F] E)
    (h : ∀ Y, L (BR R σ J X Y) = 0) : X = 0 := by sorry
