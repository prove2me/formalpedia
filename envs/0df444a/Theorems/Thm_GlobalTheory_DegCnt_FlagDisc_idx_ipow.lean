-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_FlagDisc_idx_ipow
-- name    : GlobalTheory.DegCnt.FlagDisc.idx_ipow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:22:02.259807+00:00
-- url     : https://prove2.me/theorems/b20a8074-390b-4e1d-9366-e63748f334cf
-- title:
--   Flag Disc: idx ipow
-- statement:
--   The Flag Disc construction uses the idx ipow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFlagPairLatticeSumDiscriminantEqNormMinor.lean#L35-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFlagPairLatticeSumDiscriminantEqNormMinor.lean#L35-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsStarStableIdealAbsorbingMinors
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairLatticeSumDiscriminantEqNormMinor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.FlagDisc
open GlobalTheory.DegCnt.DelScale GlobalTheory.DegCnt.Absorb
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
omit [StarRing K]

theorem GlobalTheory.DegCnt.FlagDisc.idx_ipow {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) (n : ℤ) (hn : 0 ≤ n) :
    (1 : K) ∈ ipow 𝔡 (-n) ∧ (idx (ipow 𝔡 (-n)) 1 : ℝ) = (Ideal.absNorm 𝔡 : ℝ) ^ n := by sorry
