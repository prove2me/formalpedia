-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_mat_ext
-- name    : GlobalTheory.CompanionTheory.SW.TraceCoord.mat_ext
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:11:28.622538+00:00
-- url     : https://prove2.me/theorems/c12ea014-c745-4c5b-be27-f375b9bc2393
-- title:
--   Trace Coord: mat ext
-- statement:
--   The Trace Coord construction uses the mat ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean#L87-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean#L87-L90

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

theorem GlobalTheory.CompanionTheory.SW.TraceCoord.mat_ext {n : Type} [Fintype n] [DecidableEq n] (P Q : Matrix n n R)
    (h : ∀ u v : n → R, u ⬝ᵥ (P *ᵥ v) = u ⬝ᵥ (Q *ᵥ v)) : P = Q := by sorry
