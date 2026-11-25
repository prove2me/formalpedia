-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_NormOneCount_isIntegral_of_mul_mem
-- name    : GlobalTheory.DegCnt.NormOneCount.isIntegral_of_mul_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:00:19.779136+00:00
-- url     : https://prove2.me/theorems/9fab17c3-c9bb-4e41-a251-7aadfea2778f
-- title:
--   Norm One Count: is Integral of mul mem
-- statement:
--   The Norm One Count construction uses the is Integral of mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsIntegralOfMulMem.lean#L75-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsIntegralOfMulMem.lean#L75-L87

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

theorem GlobalTheory.DegCnt.NormOneCount.isIntegral_of_mul_mem {𝔞 : Ideal (𝓞 K)} (h : 𝔞 ≠ ⊥) {u : K}
    (hu : ∀ t ∈ ipow 𝔞 1, u * t ∈ ipow 𝔞 1) : IsIntegral ℤ u := by sorry
