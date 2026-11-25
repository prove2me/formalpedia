-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_FlagDisc_idx_free
-- name    : GlobalTheory.DegCnt.FlagDisc.idx_free
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:21:13.803981+00:00
-- url     : https://prove2.me/theorems/d68aee17-a8c6-5536-af0c-793cac4ece47
-- title:
--   Flag Disc: idx free
-- statement:
--   The Flag Disc construction uses the idx free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFlagPairLatticeSumDiscriminantEqNormMinor.lean#L58-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFlagPairLatticeSumDiscriminantEqNormMinor.lean#L58-L129

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

theorem GlobalTheory.DegCnt.FlagDisc.idx_free {ι : Type} [Fintype ι] [DecidableEq ι] (x x' : ι → V) (hx : Set.range x' = Set.range x)
    (hi : ∀ p q, H.B (x p) (x' q) ∈ (1 : Submodule (𝓞 K) K))
    (hd : (Matrix.of fun p q => H.B (x p) (x' q)).det ≠ 0) :
    (∀ v ∈ Submodule.span K (Set.range x), (∀ q, H.B v (x' q) = 0) → v = 0) ∧
    (idx (dual H (Submodule.span (𝓞 K) (Set.range x))) (Submodule.span (𝓞 K) (Set.range x)) : ℝ) =
      |((Algebra.norm ℚ (Matrix.of fun p q => H.B (x p) (x' q)).det : ℚ) : ℝ)| := by sorry
