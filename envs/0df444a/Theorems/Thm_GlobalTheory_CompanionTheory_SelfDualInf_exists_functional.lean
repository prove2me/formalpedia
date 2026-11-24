-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_exists_functional
-- name    : GlobalTheory.CompanionTheory.SelfDualInf.exists_functional
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:38:44.280589+00:00
-- url     : https://prove2.me/theorems/b0cbfae1-4ad5-41e1-8773-fb29dc5c456f
-- title:
--   Self Dual Inf: exists functional
-- statement:
--   The Self Dual Inf construction uses the exists functional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/HasCoordOfFiniteDimensional.lean#L405-L427
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/HasCoordOfFiniteDimensional.lean#L405-L427

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
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.SelfDualInf.exists_functional (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    ∃ L : Ainf F →+ ℝ, Continuous L ∧
      (∀ x, psiInf F ψ x = Complex.exp ((L x : ℂ) * Complex.I)) ∧
      ∀ t, (∀ r, L (r * t) = 0) → t = 0 := by sorry
