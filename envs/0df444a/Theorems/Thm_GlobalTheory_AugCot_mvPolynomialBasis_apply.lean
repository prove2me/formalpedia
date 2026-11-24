-- Prove2me | Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
-- name    : GlobalTheory.AugCot.mvPolynomialBasis_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:46:28.816659+00:00
-- url     : https://prove2.me/theorems/7d5050d4-7d8b-4143-b4a9-61dea85045fc
-- title:
--   Aug Cot: mv Polynomial Basis apply
-- statement:
--   The Aug Cot construction uses the mv Polynomial Basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L790-L796
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L790-L796

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory
open GlobalTheory.AugCot
variable {R σ : Type*} [CommRing R] (x : σ → R)
open MvPolynomial

theorem GlobalTheory.AugCot.mvPolynomialBasis_apply (i : σ) :
    mvPolynomialBasis x i = d (aeval x : MvPolynomial σ R →ₐ[R] R) (X i) := by sorry
