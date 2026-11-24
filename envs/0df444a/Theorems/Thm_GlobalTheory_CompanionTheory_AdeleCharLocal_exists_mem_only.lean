-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_exists_mem_only
-- name    : GlobalTheory.CompanionTheory.AdeleCharLocal.exists_mem_only
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:23:37.754491+00:00
-- url     : https://prove2.me/theorems/c3b0889a-7d2c-42bb-a815-8891ed2e2d91
-- title:
--   Adele Char Local: exists mem only
-- statement:
--   The Adele Char Local construction uses the exists mem only property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/SelfDualLatticeFiltrationCharacter.lean#L270-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/SelfDualLatticeFiltrationCharacter.lean#L270-L285

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

theorem GlobalTheory.CompanionTheory.AdeleCharLocal.exists_mem_only (v : HeightOneSpectrum (𝓞 F)) :
    ∃ t : 𝓞 F, t ≠ 0 ∧ t ∈ v.asIdeal ∧ ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → t ∉ w.asIdeal := by sorry
