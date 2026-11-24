-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_hermScal_main
-- name    : GlobalTheory.CompanionTheory.SW.hermScal_main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:26.694045+00:00
-- url     : https://prove2.me/theorems/1fd0048f-feff-4560-96ac-65f790975eca
-- title:
--   SW: herm Scal main
-- statement:
--   The SW construction uses the herm Scal main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ContinuousHermScal.lean#L235-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ContinuousHermScal.lean#L235-L239

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousHermScal
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

theorem GlobalTheory.CompanionTheory.SW.hermScal_main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), IsHomeomorph (hermScal R σ) ∧ (∀ S : HermR R σ 1, hermScal R σ (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0)) = S) ∧ ∀ (lam : Measure R), lam.IsAddHaarMeasure → lam.map (hermScal R σ) = coordHerm R σ b lam 1 := by sorry
