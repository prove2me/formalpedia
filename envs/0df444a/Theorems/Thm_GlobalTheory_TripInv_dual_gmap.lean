-- Prove2me | Theorems.Thm_GlobalTheory_TripInv_dual_gmap
-- name    : GlobalTheory.TripInv.dual_gmap
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:33:54.023183+00:00
-- url     : https://prove2.me/theorems/aaeec044-39ca-48b7-8070-b00baf035d24
-- title:
--   Trip Inv: dual gmap
-- statement:
--   The Trip Inv construction uses the dual gmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsometricEmbeddedDatumPairsEncardIsometrySmul.lean#L94-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsometricEmbeddedDatumPairsEncardIsometrySmul.lean#L94-L105

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

theorem GlobalTheory.TripInv.dual_gmap {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.dual H.B.flip (Formalism.HermitianLatticesTheory.gmap s M) = Formalism.HermitianLatticesTheory.gmap s (Formalism.HermitianLatticesTheory.dual H.B.flip M) := by sorry
