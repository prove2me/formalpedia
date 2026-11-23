-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_hform_eq
-- name    : GlobalTheory.CompanionTheory.SW.TraceCoord.hform_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:42.679323+00:00
-- url     : https://prove2.me/theorems/d62122eb-6480-4f6b-a36c-6c6ace9d9b60
-- title:
--   Trace Coord: hform eq
-- statement:
--   The Trace Coord construction uses the hform eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean#L70-L72

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsTraceFormGramMatrixInBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TraceCoord
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d M : ℕ}

theorem GlobalTheory.CompanionTheory.SW.TraceCoord.hform_eq (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (x y : Fin M → A) :
    hform s J x y = (s ∘ x) ⬝ᵥ (J *ᵥ y) := by sorry
