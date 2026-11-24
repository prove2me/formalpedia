-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_CoordMat_matrix_ext_dot
-- name    : GlobalTheory.CompanionTheory.SW.CoordMat.matrix_ext_dot
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:03:04.379707+00:00
-- url     : https://prove2.me/theorems/68f83376-4a74-4e7b-90aa-62f84fc05a3b
-- title:
--   Coord Mat: matrix ext dot
-- statement:
--   The Coord Mat construction uses the matrix ext dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TraceGramDetNeZero.lean#L83-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TraceGramDetNeZero.lean#L83-L86

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

theorem GlobalTheory.CompanionTheory.SW.CoordMat.matrix_ext_dot {ι A : Type} [Fintype ι] [DecidableEq ι] [CommRing A] (P Q : Matrix ι ι A)
    (h : ∀ u v : ι → A, u ⬝ᵥ P *ᵥ v = u ⬝ᵥ Q *ᵥ v) : P = Q := by sorry
