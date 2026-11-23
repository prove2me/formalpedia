-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_dot_mulVec_left
-- name    : GlobalTheory.CompanionTheory.SW.TraceCoord.dot_mulVec_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:13.429927+00:00
-- url     : https://prove2.me/theorems/7738cbd3-88dc-4878-b1e1-8ab6d52fa5be
-- title:
--   Trace Coord: dot mul Vec left
-- statement:
--   The Trace Coord construction uses the dot mul Vec left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean#L74-L76

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

theorem GlobalTheory.CompanionTheory.SW.TraceCoord.dot_mulVec_left {n : Type} [Fintype n] (P : Matrix n n R) (u w : n → R) :
    (P *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Pᵀ *ᵥ w) := by sorry
