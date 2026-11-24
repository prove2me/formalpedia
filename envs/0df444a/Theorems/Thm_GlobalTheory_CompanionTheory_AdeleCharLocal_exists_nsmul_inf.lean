-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_exists_nsmul_inf
-- name    : GlobalTheory.CompanionTheory.AdeleCharLocal.exists_nsmul_inf
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:23:28.958413+00:00
-- url     : https://prove2.me/theorems/f2ed1dd6-b774-4e9e-b733-6f6c9df0b7d3
-- title:
--   Adele Char Local: exists nsmul inf
-- statement:
--   The Adele Char Local construction uses the exists nsmul inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/SelfDualLatticeFiltrationCharacter.lean#L113-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/SelfDualLatticeFiltrationCharacter.lean#L113-L121

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct RestrictedProduct nonZeroDivisors
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdeleCharLocal
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.AdeleCharLocal.exists_nsmul_inf {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ N : ℕ, 0 < N ∧ ∀ r : 𝓞 F, ψ (pairA F (algebraMap F _ ((N : F) * r)) 0) = 1 := by sorry
