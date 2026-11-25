-- Prove2me | Theorems.Thm_GlobalTheory_T_referenceLattice_mem_of_mem_innerSpan
-- name    : GlobalTheory.T.referenceLattice_mem_of_mem_innerSpan
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:46:34.30323+00:00
-- url     : https://prove2.me/theorems/91881e7a-bdaa-48af-bfc3-5e1885f921e4
-- title:
--   T: reference Lattice mem of mem inner Span
-- statement:
--   The T construction uses the reference Lattice mem of mem inner Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ReferenceLatticeMemOfMemInnerSpanStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ReferenceLatticeMemOfMemInnerSpanStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ReferenceLatticeMemOfMemInnerSpan
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ReferenceLatticeMemOfMemInnerSpanStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.referenceLattice_mem_of_mem_innerSpan : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : GlobalTheory.DegCnt.NF H r) (L : Submodule (𝓞 K) V), N.F.z ∈ L → ∀ v ∈ N.Ref L, v ∈ N.Wn → v ∈ L := by sorry
