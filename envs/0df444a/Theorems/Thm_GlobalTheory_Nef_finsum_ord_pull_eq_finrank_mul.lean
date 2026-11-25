-- Prove2me | Theorems.Thm_GlobalTheory_Nef_finsum_ord_pull_eq_finrank_mul
-- name    : GlobalTheory.Nef.finsum_ord_pull_eq_finrank_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:16:25.338176+00:00
-- url     : https://prove2.me/theorems/7763ff65-ae3d-4147-879d-74040d1a3ce5
-- title:
--   Nef: finsum ord pull eq finrank mul
-- statement:
--   The Nef construction uses the finsum ord pull eq finrank mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumOrderPlacesAboveEqFinrankMul.lean#L12-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumOrderPlacesAboveEqFinrankMul.lean#L12-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceSumOrderEqFinrankStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceOrderCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceRestrictionExistsPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumOrderPlacesAboveEqFinrankMul
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
open GlobalTheory GlobalTheory.Nef

theorem GlobalTheory.Nef.finsum_ord_pull_eq_finrank_mul : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → (∀ s : Set (Place k F), s.Finite → (ρ ⁻¹' s).Finite) ∧ ∀ φ : Place k F → F, {v | ord v (φ v) ≠ 0}.Finite → ∑ᶠ p : Place k E, ord p (algebraMap F E (φ (ρ p))) = Module.finrank F E * ∑ᶠ v, ord v (φ v) := by sorry
