-- Prove2me | Theorems.Thm_GlobalTheory_DegMove_isotropicNormalFormMapIsometry_baseLattice
-- name    : GlobalTheory.DegMove.isotropicNormalFormMapIsometry_baseLattice
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:00:41.250094+00:00
-- url     : https://prove2.me/theorems/d306da7d-8c37-4d09-ae58-b04bc77209ab
-- title:
--   Deg Move: isotropic Normal Form Map Isometry base Lattice
-- statement:
--   The Deg Move construction uses the isotropic Normal Form Map Isometry base Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsHermFramePairNormalFormMovedByIsometry.lean#L236-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsHermFramePairNormalFormMovedByIsometry.lean#L236-L239

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

theorem GlobalTheory.DegMove.isotropicNormalFormMapIsometry_baseLattice : (mvN hs N).P0 = s • N.P0 := by sorry
