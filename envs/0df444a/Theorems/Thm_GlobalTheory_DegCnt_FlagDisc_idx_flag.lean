-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_FlagDisc_idx_flag
-- name    : GlobalTheory.DegCnt.FlagDisc.idx_flag
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:38:15.43475+00:00
-- url     : https://prove2.me/theorems/0f93151d-3c3b-4382-9426-e5806f153e53
-- title:
--   Flag Disc: idx flag
-- statement:
--   The Flag Disc construction uses the idx flag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFlagPairLatticeSumDiscriminantEqNormMinor.lean#L152-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFlagPairLatticeSumDiscriminantEqNormMinor.lean#L152-L247

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
omit [NumberField K]

theorem GlobalTheory.DegCnt.FlagDisc.idx_flag (F : FlagD H r) (Λ : Submodule (𝓞 K) V) (y : Fin r → V) (hy : ∀ a, y a ∈ Λ)
    (he : ∀ a, F.e a.castSucc - y a ∈ F.Xa a.val) (n : ℕ → ℝ)
    (hn : ∀ a : Fin r, (idx (lead F Λ a.castSucc) 1 : ℝ) = n a.val) : ∀ l ≤ r,
    Submodule.span K (y '' {a | a.val < l}) = F.Xa l ∧
      Submodule.span (𝓞 K) (y '' {a | a.val < l}) ≤ latF F Λ l ∧
      (idx (latF F Λ l) (Submodule.span (𝓞 K) (y '' {a | a.val < l})) : ℝ) = ∏ a ∈ Finset.range l, n a := by sorry
