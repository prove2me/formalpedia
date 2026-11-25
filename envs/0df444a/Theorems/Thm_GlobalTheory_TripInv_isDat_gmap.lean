-- Prove2me | Theorems.Thm_GlobalTheory_TripInv_isDat_gmap
-- name    : GlobalTheory.TripInv.isDat_gmap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:34:23.177157+00:00
-- url     : https://prove2.me/theorems/cca951a4-19b8-4adb-9566-60a7ee2ffae2
-- title:
--   Trip Inv: is Dat gmap
-- statement:
--   The Trip Inv construction uses the is Dat gmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsometricEmbeddedDatumPairsEncardIsometrySmul.lean#L166-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsometricEmbeddedDatumPairsEncardIsometrySmul.lean#L166-L174

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

theorem GlobalTheory.TripInv.isDat_gmap {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) {g : ℕ} {L : Submodule (𝓞 K) V}
    {j x : ℕ} {d : Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)} (h : IsDat H g L j x d) :
    IsDat H g (Formalism.HermitianLatticesTheory.gmap s L) j x (Formalism.HermitianLatticesTheory.gmap s d.1, pmap s d.2) := by sorry
