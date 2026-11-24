-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TopH_topH_props
-- name    : GlobalTheory.CompanionTheory.SW.TopH.topH_props
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:56.765385+00:00
-- url     : https://prove2.me/theorems/3ca051a2-f1ce-4e2d-b121-29f092c2d0f3
-- title:
--   Top H: top H props
-- statement:
--   The Top H construction uses the top H props property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryGroupLocallyCompact.lean#L44-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryGroupLocallyCompact.lean#L44-L81

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TopH
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem GlobalTheory.CompanionTheory.SW.TopH.topH_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R], IsTopologicalGroup (HA R σ J) ∧ LocallyCompactSpace (HA R σ J) ∧ SecondCountableTopology (HA R σ J) ∧ T2Space (HA R σ J) ∧ BorelSpace (HA R σ J) ∧ ∀ n : ℕ, (Continuous fun p : HA R σ J × (Fin n → Fin M → R ⊗[F] E) => actW R σ J p.1 p.2) ∧ (∀ X : Fin n → Fin M → R ⊗[F] E, actW R σ J 1 X = X) ∧ (∀ (g h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), actW R σ J (g * h) X = actW R σ J g (actW R σ J h X)) ∧ ∀ (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), gramR R σ J (actW R σ J h X) = gramR R σ J X := by sorry
