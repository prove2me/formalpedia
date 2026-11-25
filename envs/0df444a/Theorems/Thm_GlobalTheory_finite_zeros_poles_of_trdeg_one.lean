-- Prove2me | Theorems.Thm_GlobalTheory_finite_zeros_poles_of_trdeg_one
-- name    : GlobalTheory.finite_zeros_poles_of_trdeg_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:56:24.802833+00:00
-- url     : https://prove2.me/theorems/6f4daf6e-e8d8-4a78-b5c6-f267a50357a7
-- title:
--   Global Theory: finite zeros poles of trdeg one
-- statement:
--   The Global Theory construction uses the finite zeros poles of trdeg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FiniteNormDiscreteNeZeroOfIsDedekindDomain.lean#L61-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FiniteNormDiscreteNeZeroOfIsDedekindDomain.lean#L61-L111

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FiniteNormDiscreteNeZeroOfIsDedekindDomain
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
open scoped IntermediateField.algebraAdjoinAdjoin

theorem GlobalTheory.finite_zeros_poles_of_trdeg_one :
    ∀ (F Ω : Type) [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (t : Ω),
      (⊤ : IntermediateField F Ω).FG → Algebra.trdeg F Ω = 1 → Transcendental F t →
      ∀ g : Ω, g ≠ 0 → {v : AddValuation Ω (WithTop ℤ) |
        IsNormDiscrete v ∧ IsTrivOn F v ∧ 0 ≤ v t ∧ v g ≠ 0}.Finite := by sorry
