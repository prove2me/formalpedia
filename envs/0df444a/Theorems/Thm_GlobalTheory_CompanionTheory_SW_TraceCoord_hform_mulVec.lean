-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_hform_mulVec
-- name    : GlobalTheory.CompanionTheory.SW.TraceCoord.hform_mulVec
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:11:28.965362+00:00
-- url     : https://prove2.me/theorems/5da384cb-a3ef-4c3d-97e0-4467a3ff8960
-- title:
--   Trace Coord: hform mul Vec
-- statement:
--   The Trace Coord construction uses the hform mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean#L78-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean#L78-L85

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

theorem GlobalTheory.CompanionTheory.SW.TraceCoord.hform_mulVec (s : A →+* A) (J H : Matrix (Fin M) (Fin M) A)
    (hH : cT s H * J * H = J) (x y : Fin M → A) :
    hform s J (H *ᵥ x) (H *ᵥ y) = hform s J x y := by sorry
