-- Prove2me | Theorems.Thm_GlobalTheory_WeberCubicAlgebra_cubic_eq
-- name    : GlobalTheory.WeberCubicAlgebra.cubic_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T05:32:43.691198+00:00
-- url     : https://prove2.me/theorems/0ab1d8f7-a4cf-4f80-82e9-942ef401c8a2
-- title:
--   Weber Cubic Algebra: cubic eq
-- statement:
--   The Weber Cubic Algebra construction uses the cubic eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeberFunctionsRootsOfCubicOfHalfPeriodDiff.lean#L62-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeberFunctionsRootsOfCubicOfHalfPeriodDiff.lean#L62-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeberFunctionsRootsOfCubicOfHalfPeriodDiff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open Polynomial
open UpperHalfPlane hiding I
noncomputable section
open GlobalTheory GlobalTheory.WeberCubicAlgebra

theorem GlobalTheory.WeberCubicAlgebra.cubic_eq (j F0 F1 F2 : ℂ)
    (h : F0 - F1 - F2 = 48 ∧ -(F0 * F1) - F0 * F2 + F1 * F2 = 768 - j ∧ F0 * F1 * F2 = 4096) :
    ((X - C 16) ^ 3 - C j * X : ℂ[X]) = (X - C F0) * (X - C (-F1)) * (X - C (-F2)) := by sorry
