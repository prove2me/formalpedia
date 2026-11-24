-- Prove2me | Theorems.Thm_GlobalTheory_StabFlat_localization_of_isStandardSmooth
-- name    : GlobalTheory.StabFlat.localization_of_isStandardSmooth
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:23:57.226005+00:00
-- url     : https://prove2.me/theorems/9eb53bf0-78c5-4676-b283-9363137d4534
-- title:
--   Stab Flat: localization of is Standard Smooth
-- statement:
--   The Stab Flat construction uses the localization of is Standard Smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LocalizationOfIsStandardSmooth.lean#L97-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LocalizationOfIsStandardSmooth.lean#L97-L150

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPushoutQuotientMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocalizationOfIsStandardSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.StabFlat

theorem GlobalTheory.StabFlat.localization_of_isStandardSmooth {V R A : Type} [CommRing V] [IsNoetherianRing V] [CommRing R] [CommRing A]
    {ϖ : V} (h₀ : ϖ ∈ nonZeroDivisors V) [(Ideal.span {ϖ}).IsMaximal] {g : ℕ} {ρ : V →+* R}
    (hρ : ρ.IsStandardSmoothOfRelativeDimension g) (n : Ideal R) [n.IsMaximal] [Algebra R A]
    [IsLocalization.AtPrime A n] (hn : ρ ϖ ∈ n) :
    IsNoetherianRing A ∧ algebraMap R A (ρ ϖ) ∈ nonZeroDivisors A ∧
      IsRegularLocalRing (A ⧸ Ideal.span {algebraMap R A (ρ ϖ)}) ∧
      ringKrullDim (A ⧸ Ideal.span {algebraMap R A (ρ ϖ)}) = g := by sorry
