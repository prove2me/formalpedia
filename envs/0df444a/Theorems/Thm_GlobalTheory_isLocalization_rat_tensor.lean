-- Prove2me | Theorems.Thm_GlobalTheory_isLocalization_rat_tensor
-- name    : GlobalTheory.isLocalization_rat_tensor
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:58:38.850794+00:00
-- url     : https://prove2.me/theorems/87b52d5c-ec15-45a2-88ff-3f4c6c9b60e4
-- title:
--   Global Theory: is Localization rat tensor
-- statement:
--   The Global Theory construction uses the is Localization rat tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalMaxPrincipleWeightedFiniteTypeInt.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalMaxPrincipleWeightedFiniteTypeInt.lean#L8-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalMaximumPrincipleWeightFiniteMvPolynomialStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalMaxPrincipleWeightedFiniteTypeInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.isLocalization_rat_tensor (B : Type) [CommRing B] :
    letI := Algebra.TensorProduct.rightAlgebra (R := ℤ) (A := ℚ) (B := B)
    IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ)) (ℚ ⊗[ℤ] B) := by sorry
