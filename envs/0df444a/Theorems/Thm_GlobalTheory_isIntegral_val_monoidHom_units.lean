-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_val_monoidHom_units
-- name    : GlobalTheory.isIntegral_val_monoidHom_units
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:56:53.527804+00:00
-- url     : https://prove2.me/theorems/1994a55e-0e10-41f5-b444-b23b02fc3b0a
-- title:
--   Global Theory: is Integral val monoid Hom units
-- statement:
--   The Global Theory construction uses the is Integral val monoid Hom units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ComplexMatrixGaussSumNormIntegralGalois.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ComplexMatrixGaussSumNormIntegralGalois.lean#L20-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixGaussSumSingularAndInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixGaussSumMulDualEqCardPowSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComplexMatrixGaussSumNormIntegralGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped TensorProduct Classical
open GlobalTheory

theorem GlobalTheory.isIntegral_val_monoidHom_units {G : Type} [Group G] [Finite G] (ξ : G →* ℂˣ) (g : G) :
    IsIntegral ℤ ((ξ g : ℂˣ) : ℂ) := by sorry
