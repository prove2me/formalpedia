-- Prove2me | Theorems.Thm_GlobalTheory_WeberCubicAlgebra_half_root
-- name    : GlobalTheory.WeberCubicAlgebra.half_root
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T05:33:23.149292+00:00
-- url     : https://prove2.me/theorems/9eee92a0-b1d7-45e5-b9b4-c83aca65374a
-- title:
--   Weber Cubic Algebra: half root
-- statement:
--   The Weber Cubic Algebra construction uses the half root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeberFunctionsRootsOfCubicOfHalfPeriodDiff.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeberFunctionsRootsOfCubicOfHalfPeriodDiff.lean#L14-L22

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

theorem GlobalTheory.WeberCubicAlgebra.half_root (L : PeriodPair) {t : ℂ} (h2 : 2 * t ∈ L.lattice) (ht : t ∉ L.lattice) :
    4 * L.weierstrassP t ^ 3 - L.g₂ * L.weierstrassP t - L.g₃ = 0 := by sorry
