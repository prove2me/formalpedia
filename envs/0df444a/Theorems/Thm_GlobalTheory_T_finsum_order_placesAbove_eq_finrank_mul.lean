-- Prove2me | Theorems.Thm_GlobalTheory_T_finsum_order_placesAbove_eq_finrank_mul
-- name    : GlobalTheory.T.finsum_order_placesAbove_eq_finrank_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:32:17.365584+00:00
-- url     : https://prove2.me/theorems/27ac0635-7442-4051-bb37-53e531687a0a
-- title:
--   T: finsum order places Above eq finrank mul
-- statement:
--   The T construction uses the finsum order places Above eq finrank mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumOrderPlacesAboveEqFinrankMulStatement.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumOrderPlacesAboveEqFinrankMulStatement.lean#L10-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumOrderPlacesAboveEqFinrankMul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumOrderPlacesAboveEqFinrankMulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finsum_order_placesAbove_eq_finrank_mul : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → (∀ s : Set (Place k F), s.Finite → (ρ ⁻¹' s).Finite) ∧ ∀ φ : Place k F → F, {v | ord v (φ v) ≠ 0}.Finite → ∑ᶠ p : Place k E, ord p (algebraMap F E (φ (ρ p))) = Module.finrank F E * ∑ᶠ v, ord v (φ v) := by sorry
