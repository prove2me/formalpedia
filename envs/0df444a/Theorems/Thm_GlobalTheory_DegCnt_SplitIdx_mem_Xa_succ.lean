-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_mem_Xa_succ
-- name    : GlobalTheory.DegCnt.SplitIdx.mem_Xa_succ
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:26:17.708459+00:00
-- url     : https://prove2.me/theorems/b897b244-4759-46d8-b0b4-a287e6530670
-- title:
--   Split Idx: mem Xa succ
-- statement:
--   The Split Idx construction uses the mem Xa succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormTerminalDeterminant.lean#L127-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormTerminalDeterminant.lean#L127-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairLatticeSumDiscriminantEqNormMinorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormTerminalDeterminant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.SplitIdx
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder GlobalTheory.DegCnt.DelScale
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {r : ℕ}
omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem GlobalTheory.DegCnt.SplitIdx.mem_Xa_succ (F : FlagD H r) (a : Fin r) {x : V} (hx : x ∈ F.Xa (a.val + 1)) :
    ∃ t : K, x - t • F.e a.castSucc ∈ F.Xa a.val := by sorry
