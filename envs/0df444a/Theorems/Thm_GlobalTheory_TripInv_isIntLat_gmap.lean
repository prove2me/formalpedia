-- Prove2me | Theorems.Thm_GlobalTheory_TripInv_isIntLat_gmap
-- name    : GlobalTheory.TripInv.isIntLat_gmap
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:34:43.95344+00:00
-- url     : https://prove2.me/theorems/07e03f51-1be2-4515-b329-43235bb2a888
-- title:
--   Trip Inv: is Int Lat gmap
-- statement:
--   The Trip Inv construction uses the is Int Lat gmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsometricEmbeddedDatumPairsEncardIsometrySmul.lean#L107-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsometricEmbeddedDatumPairsEncardIsometrySmul.lean#L107-L121

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

theorem GlobalTheory.TripInv.isIntLat_gmap {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) {M : Submodule (𝓞 K) V}
    (hM : GlobalTheory.Mass.IsIntLat H.B.flip M) : GlobalTheory.Mass.IsIntLat H.B.flip (Formalism.HermitianLatticesTheory.gmap s M) := by sorry
