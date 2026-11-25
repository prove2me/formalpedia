-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_step
-- name    : GlobalTheory.DegCnt.SplitIdx.step
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:27:48.17274+00:00
-- url     : https://prove2.me/theorems/ecdf0096-8874-4968-850d-ccbb500cf67e
-- title:
--   Split Idx: step
-- statement:
--   The Split Idx construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormTerminalDeterminant.lean#L185-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormTerminalDeterminant.lean#L185-L212

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
omit [NumberField K] [FiniteDimensional K V]

theorem GlobalTheory.DegCnt.SplitIdx.step (F : FlagD H r) {Λ J : Submodule (𝓞 K) V} (hJ : J ≤ Λ) (a : Fin r) :
    idx (latF F Λ (a.val + 1) ⊔ J) (latF F Λ a.val ⊔ J) = idx (lead F Λ a.castSucc) (lead F J a.castSucc) := by sorry
