-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_lintegral_haarGLReal_iwasawa
-- name    : GroundTheory.Automorphic.lintegral_haarGLReal_iwasawa
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:54:01.25851+00:00
-- url     : https://prove2.me/theorems/a8d78442-9649-5733-a226-531ce50a9ee3
-- title:
--   Automorphic: lintegral haar GLReal iwasawa
-- statement:
--   The Automorphic construction uses the lintegral haar GLReal iwasawa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsIwasawaHaar.lean#L201-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsIwasawaHaar.lean#L201-L213

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawaHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix Set
open scoped ComplexOrder
set_option linter.unusedSectionVars false
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]
open MeasureTheory Measure
open scoped ENNReal NNReal Matrix.Norms.L2Operator
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem GroundTheory.Automorphic.lintegral_haarGLReal_iwasawa (μ₀ : Measure (Matrix n n ℝ)) [μ₀.IsAddHaarMeasure]
    (μK : Measure (unitaryGroup n ℝ)) [μK.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n ℝ)) [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL n ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂(haarGLReal μ₀) =
        c * ∫⁻ k, ∫⁻ b, f (Unitary.toUnits k * b) ∂μB.inv ∂μK := by sorry
