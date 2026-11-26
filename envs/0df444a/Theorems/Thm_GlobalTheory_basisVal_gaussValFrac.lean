-- Prove2me | Theorems.Thm_GlobalTheory_basisVal_gaussValFrac
-- name    : GlobalTheory.basisVal_gaussValFrac
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:43:35.373653+00:00
-- url     : https://prove2.me/theorems/b6a1b807-6e22-40ed-b1d5-ba2762139c03
-- title:
--   Global Theory: basis Val gauss Val Frac
-- statement:
--   The Global Theory construction uses the basis Val gauss Val Frac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L977-L985
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L977-L985

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open MvPolynomial Module IsDedekindDomain

theorem GlobalTheory.basisVal_gaussValFrac {O K Γ₀ ι σ F M : Type*} [CommRing O] [Field K] [Algebra O K]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) [Field F]
    [Algebra (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F] [Algebra O F]
    [IsScalarTower O (MvPolynomial σ K) F] [AddCommGroup M] [Module O M] (b : Basis ι O M)
    (x : MvPolynomial σ K ⊗[O] M) :
    basisVal (gaussValFrac v σ F) (b.baseChange F)
      ((IsScalarTower.toAlgHom O (MvPolynomial σ K) F).toLinearMap.rTensor M x) =
      tensorContent v b x := by sorry
