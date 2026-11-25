-- Prove2me | Theorems.Thm_GlobalTheory_DegAsm_AdaptInv_flagFramesSameGraded_definitePartLattice_eq
-- name    : GlobalTheory.DegAsm.AdaptInv.flagFramesSameGraded_definitePartLattice_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:26:21.653272+00:00
-- url     : https://prove2.me/theorems/3f69ab72-7c9c-4417-9787-180e5c37b7e8
-- title:
--   Adapt Inv: flag Frames Same Graded definite Part Lattice eq
-- statement:
--   The Adapt Inv construction uses the flag Frames Same Graded definite Part Lattice eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FlagFramesSameGradedDefinitePartLatticeEq.lean#L285-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FlagFramesSameGradedDefinitePartLatticeEq.lean#L285-L289

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
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
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.AdaptInv
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V]
open NumberField
open scoped Pointwise ENNReal Classical
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}
variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V]

theorem GlobalTheory.DegAsm.AdaptInv.flagFramesSameGraded_definitePartLattice_eq {F G F' G' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G) (h' : _root_.GlobalTheory.DegAsm.SameGr F' G') (Λ : Submodule R V) :
    _root_.GlobalTheory.HermLat.flagPairDefinitePartLattice G G' Λ = _root_.GlobalTheory.HermLat.flagPairDefinitePartLattice F F' Λ := by sorry
