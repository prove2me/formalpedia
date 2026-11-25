-- Prove2me | Theorems.Thm_GlobalTheory_DegMove_span_smul
-- name    : GlobalTheory.DegMove.span_smul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:56:11.145263+00:00
-- url     : https://prove2.me/theorems/ba19e00e-c903-4569-b3ee-40f3c58a741d
-- title:
--   Deg Move: span smul
-- statement:
--   The Deg Move construction uses the span smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsHermFramePairNormalFormMovedByIsometry.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsHermFramePairNormalFormMovedByIsometry.lean#L79-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsHermFramePairNormalFormMovedByIsometry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.DegMove
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ} {s : V ≃ₗ[K] V}
omit [StarRing K]

theorem GlobalTheory.DegMove.span_smul (s : V ≃ₗ[K] V) (A : Submodule R V) :
    Submodule.span K ((s • A : Submodule R V) : Set V) = s • Submodule.span K (A : Set V) := by sorry
