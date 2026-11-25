-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_isLattice_field
-- name    : GlobalTheory.DegCnt.SplitIdx.isLattice_field
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:02:06.53913+00:00
-- url     : https://prove2.me/theorems/4e47b445-4a31-4bd5-bdd2-043105f063ca
-- title:
--   Split Idx: is Lattice field
-- statement:
--   The Split Idx construction uses the is Lattice field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormTerminalDeterminant.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormTerminalDeterminant.lean#L67-L72

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
omit [StarRing K]

theorem GlobalTheory.DegCnt.SplitIdx.isLattice_field {M : Submodule (𝓞 K) K} (hfg : M.FG) {x : K} (hx : x ∈ M) (h0 : x ≠ 0) :
    Submodule.IsLattice K M := by sorry
