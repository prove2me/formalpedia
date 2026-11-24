-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LenFib_exists_bump
-- name    : GlobalTheory.CompanionTheory.SW.LenFib.exists_bump
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:06:21.988287+00:00
-- url     : https://prove2.me/theorems/e7ecc70e-072d-448c-9f46-61af9883d7b7
-- title:
--   Len Fib: exists bump
-- statement:
--   The Len Fib construction uses the exists bump property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsFibreFamilyLength.lean#L89-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsFibreFamilyLength.lean#L89-L95

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousHermScal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsFibreFamilyLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LenFib
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]

theorem GlobalTheory.CompanionTheory.SW.LenFib.exists_bump [TopologicalSpace R] [LocallyCompactSpace R] [T2Space R]
    (hU : IsOpen {c : R | IsUnit c}) {c₀ : R} (hc₀ : IsUnit c₀) :
    ∃ χ : R → ℝ, Continuous χ ∧ tsupport χ ⊆ {c : R | IsUnit c} ∧ ∀ᶠ c in 𝓝 c₀, χ c = 1 := by sorry
