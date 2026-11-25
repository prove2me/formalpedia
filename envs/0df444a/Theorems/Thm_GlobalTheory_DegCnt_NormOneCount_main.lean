-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_NormOneCount_main
-- name    : GlobalTheory.DegCnt.NormOneCount.main
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:25:25.707803+00:00
-- url     : https://prove2.me/theorems/824a2825-2a98-5c72-b941-7baa9d3b3a21
-- title:
--   Norm One Count: main
-- statement:
--   The Norm One Count construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsIntegralOfMulMem.lean#L116-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsIntegralOfMulMem.lean#L116-L156

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfMulMem
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.NormOneCount
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.DegCnt.NormOneCount.main : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ x : ℝ, 1 ≤ x → ((({c : K | c * star c = 1 ∧ ∃ 𝔞 𝔞' : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ 𝔞' ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ x ∧ (Ideal.absNorm 𝔞' : ℝ) ≤ x ∧ ∀ t : K, t * c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (8 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) ^ 2 * x ^ (2 * (2 + cf K))) := by sorry
