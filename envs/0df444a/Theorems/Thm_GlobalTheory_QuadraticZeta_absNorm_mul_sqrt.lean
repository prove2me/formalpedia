-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticZeta_absNorm_mul_sqrt
-- name    : GlobalTheory.QuadraticZeta.absNorm_mul_sqrt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:13.769601+00:00
-- url     : https://prove2.me/theorems/8e3286e8-c60a-4a15-9108-328d6d1b1a60
-- title:
--   Quadratic Zeta: abs Norm mul sqrt
-- statement:
--   The Quadratic Zeta construction uses the abs Norm mul sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsBasisEmbedding.lean#L71-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsBasisEmbedding.lean#L71-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal
open scoped nonZeroDivisors UpperHalfPlane ComplexConjugate
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
variable (h2 : finrank ℚ K = 2) (hD : discr K = -d) (σ : K →+* ℂ)
include h2 hD

theorem GlobalTheory.QuadraticZeta.absNorm_mul_sqrt (I : FractionalIdeal (𝓞 K)⁰ K)
    (bI : Basis (Fin 2) ℤ (I : Submodule (𝓞 K) K)) :
    (absNorm I : ℝ) * (√d / 2) = |(σ (bI 1) * conj (σ (bI 0))).im| := by sorry
