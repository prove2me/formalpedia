-- Prove2me | Theorems.Thm_GlobalTheory_TripInv_encard_le
-- name    : GlobalTheory.TripInv.encard_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:34:04.093663+00:00
-- url     : https://prove2.me/theorems/b22e32a3-9697-4361-882a-eda80eb07b10
-- title:
--   Trip Inv: encard le
-- statement:
--   The Trip Inv construction uses the encard le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsometricEmbeddedDatumPairsEncardIsometrySmul.lean#L202-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsometricEmbeddedDatumPairsEncardIsometrySmul.lean#L202-L204

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometricEmbeddedDatumPairsEncardIsometrySmul
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
open GlobalTheory GlobalTheory.TripInv
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V}

theorem GlobalTheory.TripInv.encard_le (HW : HermSpace K V) (g j x x' : ℕ) (s : Formalism.HermitianLatticesTheory.isom HW.B.flip) (L : Submodule (𝓞 K) V) :
    (Trip HW g L j x x').encard ≤ (Trip HW g (s • L) j x x').encard := by sorry
