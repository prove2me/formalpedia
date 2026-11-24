-- Prove2me | Theorems.Thm_GlobalTheory_AnisoSize_exists_small_generator
-- name    : GlobalTheory.AnisoSize.exists_small_generator
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:58:24.661748+00:00
-- url     : https://prove2.me/theorems/467e6d67-13ca-4beb-a72e-7c03c0a330f7
-- title:
--   Aniso Size: exists small generator
-- statement:
--   The Aniso Size construction uses the exists small generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AnisotropicFiniteLengthsOfShortLatticeVector.lean#L81-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AnisotropicFiniteLengthsOfShortLatticeVector.lean#L81-L131

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AnisotropicFiniteLengthsOfShortLatticeVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix Module Submodule
open scoped ContDiff Topology nonZeroDivisors
open GlobalTheory GlobalTheory.AnisoSize
variable {E : Type} [Field E] [NumberField E]
variable (E)

theorem GlobalTheory.AnisoSize.exists_small_generator [IsTotallyComplex E] :
    ∃ (M : ℤ) (C : ℝ), M ≠ 0 ∧ ∀ J : Ideal (𝓞 E), J ≠ ⊥ →
      ∃ j ∈ J, j ≠ 0 ∧ house (algebraMap (𝓞 E) E j) ≤ C * Ideal.absNorm J ∧
        ∀ a ∈ J, j ∣ (M : 𝓞 E) * a := by sorry
