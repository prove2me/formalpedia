-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_exists_sdW_sdHerm
-- name    : GlobalTheory.CompanionTheory.SelfDualInf.exists_sdW_sdHerm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:01:57.032164+00:00
-- url     : https://prove2.me/theorems/ad3812a1-bde2-535e-8a23-43cb6b3e3496
-- title:
--   Self Dual Inf: exists sd W sd Herm
-- statement:
--   The Self Dual Inf construction uses the exists sd W sd Herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/HasCoordOfFiniteDimensional.lean#L431-L456
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/HasCoordOfFiniteDimensional.lean#L431-L456

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

theorem GlobalTheory.CompanionTheory.SelfDualInf.exists_sdW_sdHerm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → (∃ μ, SdW F E σ M J (Ainf F) (psiInf F ψ) n μ) ∧ ∃ ν, SdHerm F E σ (Ainf F) (psiInf F ψ) n ν := by sorry
