-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_CoordMat_trace_one_tmul
-- name    : GlobalTheory.CompanionTheory.SW.CoordMat.trace_one_tmul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:02:26.989152+00:00
-- url     : https://prove2.me/theorems/70eaa088-69b8-49c5-9d9e-6be46ada06a3
-- title:
--   Coord Mat: trace one tmul
-- statement:
--   The Coord Mat construction uses the trace one tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TraceGramDetNeZero.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TraceGramDetNeZero.lean#L15-L17

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TraceGramDetNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CoordMat
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem GlobalTheory.CompanionTheory.SW.CoordMat.trace_one_tmul [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (e : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by sorry
