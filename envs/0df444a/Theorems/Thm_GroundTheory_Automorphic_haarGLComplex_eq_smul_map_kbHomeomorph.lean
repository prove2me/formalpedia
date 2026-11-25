-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_haarGLComplex_eq_smul_map_kbHomeomorph
-- name    : GroundTheory.Automorphic.haarGLComplex_eq_smul_map_kbHomeomorph
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:22.269454+00:00
-- url     : https://prove2.me/theorems/52235dd0-b22b-4f02-bc33-bbbcc3a27c91
-- title:
--   Automorphic: haar GLComplex eq smul map kb Homeomorph
-- statement:
--   The Automorphic construction uses the haar GLComplex eq smul map kb Homeomorph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroups.lean#L78-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroups.lean#L78-L114

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

theorem GroundTheory.Automorphic.haarGLComplex_eq_smul_map_kbHomeomorph (μ₀ : Measure (Matrix n n ℂ)) [μ₀.IsAddHaarMeasure]
    (μK : Measure (unitaryGroup n ℂ)) [μK.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n ℂ)) [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧
      haarGLComplex μ₀ = c • Measure.map kbHomeomorph (μK.prod μB.inv) := by sorry
