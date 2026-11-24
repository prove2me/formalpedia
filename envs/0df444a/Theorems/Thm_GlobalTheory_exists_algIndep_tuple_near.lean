-- Prove2me | Theorems.Thm_GlobalTheory_exists_algIndep_tuple_near
-- name    : GlobalTheory.exists_algIndep_tuple_near
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:30:53.235209+00:00
-- url     : https://prove2.me/theorems/bfafcdbc-1f39-4111-82f7-28d164abcecd
-- title:
--   Global Theory: exists alg Indep tuple near
-- statement:
--   The Global Theory construction uses the exists alg Indep tuple near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/DenseMvPolynomialEvalNeZero.lean#L27-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/DenseMvPolynomialEvalNeZero.lean#L27-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_DenseMvPolynomialEvalNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_algIndep_tuple_near :
    ∀ (K : Type) [Field K] [Countable K] (sg : K →+* ℂ) (D : ℕ) (z₀ : Fin D → ℂ) (ε : ℝ), 0 < ε → ∃ z : Fin D → ℂ, (∀ i, ‖z i - z₀ i‖ < ε) ∧ ∀ p : MvPolynomial (Fin D) K, p ≠ 0 → MvPolynomial.eval₂ sg z p ≠ 0 := by sorry
