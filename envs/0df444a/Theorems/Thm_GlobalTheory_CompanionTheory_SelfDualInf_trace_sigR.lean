-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_trace_sigR
-- name    : GlobalTheory.CompanionTheory.SelfDualInf.trace_sigR
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:38:20.139002+00:00
-- url     : https://prove2.me/theorems/12c86a3a-cac9-4776-ad02-f7501c8164af
-- title:
--   Self Dual Inf: trace sig R
-- statement:
--   The Self Dual Inf construction uses the trace sig R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/HasCoordOfFiniteDimensional.lean#L163-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/HasCoordOfFiniteDimensional.lean#L163-L171

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

theorem GlobalTheory.CompanionTheory.SelfDualInf.trace_sigR (hσ : ∀ x, σ (σ x) = x) (z : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ z) = Algebra.trace R (R ⊗[F] E) z := by sorry
