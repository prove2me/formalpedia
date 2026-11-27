-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_lintegral_haarGLComplex_iwasawa
-- name    : GroundTheory.Automorphic.lintegral_haarGLComplex_iwasawa
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:54:16.743289+00:00
-- url     : https://prove2.me/theorems/ea940bea-2d26-5995-9e98-1cb0fa2367be
-- title:
--   Automorphic: lintegral haar GLComplex iwasawa
-- statement:
--   The Automorphic construction uses the lintegral haar GLComplex iwasawa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroups.lean#L116-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroups.lean#L116-L128

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsPolar
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsKAK
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawaHaar
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroups
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
variable {n : Type*} [Fintype n] [LinearOrder n]
open MeasureTheory Measure
open scoped ENNReal NNReal Matrix.Norms.L2Operator
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem GroundTheory.Automorphic.lintegral_haarGLComplex_iwasawa (μ₀ : Measure (Matrix n n ℂ)) [μ₀.IsAddHaarMeasure]
    (μK : Measure (unitaryGroup n ℂ)) [μK.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n ℂ)) [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL n ℂ → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂(haarGLComplex μ₀) =
        c * ∫⁻ k, ∫⁻ b, f (Unitary.toUnits k * b) ∂μB.inv ∂μK := by sorry
