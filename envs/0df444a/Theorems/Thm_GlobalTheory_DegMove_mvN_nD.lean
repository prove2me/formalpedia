-- Prove2me | Theorems.Thm_GlobalTheory_DegMove_mvN_nD
-- name    : GlobalTheory.DegMove.mvN_nD
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:01:17.921716+00:00
-- url     : https://prove2.me/theorems/f0da33bb-6c17-50f5-a731-a6cabdcd1451
-- title:
--   Deg Move: mv N n D
-- statement:
--   The Deg Move construction uses the mv N n D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsHermFramePairNormalFormMovedByIsometry.lean#L276-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsHermFramePairNormalFormMovedByIsometry.lean#L276-L280

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
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} {s : V ≃ₗ[K] V}
variable (hs : s ∈ isomGrp H) (N : NF H r)

theorem GlobalTheory.DegMove.mvN_nD (l : ℕ) : (mvN hs N).nD l = N.nD l := by sorry
