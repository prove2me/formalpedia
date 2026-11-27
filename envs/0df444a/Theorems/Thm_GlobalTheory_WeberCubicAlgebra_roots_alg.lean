-- Prove2me | Theorems.Thm_GlobalTheory_WeberCubicAlgebra_roots_alg
-- name    : GlobalTheory.WeberCubicAlgebra.roots_alg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T05:32:41.385945+00:00
-- url     : https://prove2.me/theorems/decf615a-34a9-4f25-a9b4-9986db144f45
-- title:
--   Weber Cubic Algebra: roots alg
-- statement:
--   The Weber Cubic Algebra construction uses the roots alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeberFunctionsRootsOfCubicOfHalfPeriodDiff.lean#L24-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeberFunctionsRootsOfCubicOfHalfPeriodDiff.lean#L24-L48

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

theorem GlobalTheory.WeberCubicAlgebra.roots_alg {e1 e2 e3 g h P A B D : ℂ} (h12 : e1 ≠ e2) (h13 : e1 ≠ e3) (h23 : e2 ≠ e3)
    (r1 : 4 * e1 ^ 3 - g * e1 - h = 0) (r2 : 4 * e2 ^ 3 - g * e2 - h = 0)
    (r3 : 4 * e3 ^ 3 - g * e3 - h = 0)
    (d1 : e1 - e2 = P * A) (d2 : e1 - e3 = P * B) (d3 : e3 - e2 = P * D) :
    g = 2 / 3 * P ^ 2 * (A ^ 2 + B ^ 2 + D ^ 2) ∧
      g ^ 3 - 27 * h ^ 2 = 16 * P ^ 6 * (A * B * D) ^ 2 := by sorry
