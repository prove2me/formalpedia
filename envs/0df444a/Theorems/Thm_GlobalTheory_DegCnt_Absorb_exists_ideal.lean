-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_Absorb_exists_ideal
-- name    : GlobalTheory.DegCnt.Absorb.exists_ideal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:15:23.601374+00:00
-- url     : https://prove2.me/theorems/50e00a60-8361-4e06-9d45-e21eb8dc7173
-- title:
--   Absorb: exists ideal
-- statement:
--   The Absorb construction uses the exists ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsStarStableIdealAbsorbingMinors.lean#L355-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsStarStableIdealAbsorbingMinors.lean#L355-L402

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsStarStableIdealAbsorbingMinors
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Absorb
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
open NumberField
open scoped Pointwise ENNReal Classical nonZeroDivisors
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}

theorem GlobalTheory.DegCnt.Absorb.exists_ideal (N : _root_.GlobalTheory.DegCnt.NF H r) {Λ : Submodule (𝓞 K) V}
    (h : _root_.GlobalTheory.HermLat.IsFramed N.F N.F' Λ N.aa) (l : ℕ) :
    ∃ A : Ideal (𝓞 K), A ≠ ⊥ ∧ ∀ hl : l ≤ r + 1, l ≤ N.j → _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl ≠ 0 →
      (Ideal.absNorm A : ℝ) = N.nD l ∧ ∀ x ∈ A, ∀ y ∈ _root_.GlobalTheory.DegCnt.ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)),
        (x : K) * y / _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) := by sorry
