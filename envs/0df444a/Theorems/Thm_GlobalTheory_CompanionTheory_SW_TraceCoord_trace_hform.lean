-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_trace_hform
-- name    : GlobalTheory.CompanionTheory.SW.TraceCoord.trace_hform
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:32.670743+00:00
-- url     : https://prove2.me/theorems/b724b119-56c1-4b79-a5dc-2bc3685bbb30
-- title:
--   Trace Coord: trace hform
-- statement:
--   The Trace Coord construction uses the trace hform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean#L22-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean#L22-L47

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

theorem GlobalTheory.CompanionTheory.SW.TraceCoord.trace_hform (s : A →+* A) (hs : ∀ (r : R) (a : A), s (r • a) = r • s a)
    (β : Module.Basis (Fin d) R A) (J : Matrix (Fin M) (Fin M) A) (x y : Fin M → A) :
    Algebra.trace R A (hform s J x y) = coord β x ⬝ᵥ (gramB s β J *ᵥ coord β y) := by sorry
