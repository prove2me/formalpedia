-- Prove2me | Theorems.Thm_GlobalTheory_DegAsm_AdaptInv_lead_eq
-- name    : GlobalTheory.DegAsm.AdaptInv.lead_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:26:06.7966+00:00
-- url     : https://prove2.me/theorems/8ec90cd0-33a6-5c1c-9e5a-e7018c0e238b
-- title:
--   Adapt Inv: lead eq
-- statement:
--   The Adapt Inv construction uses the lead eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FlagFramesSameGradedDefinitePartLatticeEq.lean#L223-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FlagFramesSameGradedDefinitePartLatticeEq.lean#L223-L238

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

theorem GlobalTheory.DegAsm.AdaptInv.lead_eq {F G : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r}
    (h : _root_.GlobalTheory.DegAsm.SameGr F G) (Λ : Submodule R V) (a : Fin (r + 1)) :
    _root_.GlobalTheory.HermLat.lead G Λ a = _root_.GlobalTheory.HermLat.lead F Λ a := by sorry
