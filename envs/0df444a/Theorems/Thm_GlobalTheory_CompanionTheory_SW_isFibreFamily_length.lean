-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_isFibreFamily_length
-- name    : GlobalTheory.CompanionTheory.SW.isFibreFamily_length
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:12:02.413739+00:00
-- url     : https://prove2.me/theorems/db8e5b6a-2f0a-4874-ac50-8c98fa2da4f4
-- title:
--   SW: is Fibre Family length
-- statement:
--   The SW construction uses the is Fibre Family length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsFibreFamilyLength.lean#L101-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsFibreFamilyLength.lean#L101-L166

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
open GlobalTheory.CompanionTheory.SW.LenFib

theorem GlobalTheory.CompanionTheory.SW.isFibreFamily_length : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure R), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ν {c | ¬ IsUnit c} = 0 → μ {X | ¬ IsUnit ((fun X : Fin 1 → Fin M → R ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (R) σ J (X 0)) X)} = 0 → ∀ m, IsGramFib R σ J 1 μ (ν.map (hermScal R σ)) m → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (fun X : Fin 1 → Fin M → R ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (R) σ J (X 0)) id Set.univ ν {c | IsUnit c} (fun c => m (hermScal R σ c)) := by sorry
