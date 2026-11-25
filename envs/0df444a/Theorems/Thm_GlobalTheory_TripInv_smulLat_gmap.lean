-- Prove2me | Theorems.Thm_GlobalTheory_TripInv_smulLat_gmap
-- name    : GlobalTheory.TripInv.smulLat_gmap
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:47.230099+00:00
-- url     : https://prove2.me/theorems/1890e26c-47e8-45a7-a3d1-46a4667714e5
-- title:
--   Trip Inv: smul Lat gmap
-- statement:
--   The Trip Inv construction uses the smul Lat gmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsometricEmbeddedDatumPairsEncardIsometrySmul.lean#L53-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsometricEmbeddedDatumPairsEncardIsometrySmul.lean#L53-L60

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

theorem GlobalTheory.TripInv.smulLat_gmap (s : V ≃ₗ[K] V) (g : 𝓞 K) (M : Submodule (𝓞 K) V) :
    smulLat g (Formalism.HermitianLatticesTheory.gmap s M) = Formalism.HermitianLatticesTheory.gmap s (smulLat g M) := by sorry
