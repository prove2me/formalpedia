-- Prove2me | Theorems.Thm_GlobalTheory_DetInv_ker_bC_eq_range_alC_and_ker_alC_eq_range_bC
-- name    : GlobalTheory.DetInv.ker_bC_eq_range_alC_and_ker_alC_eq_range_bC
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:06.674386+00:00
-- url     : https://prove2.me/theorems/2622853a-46e3-4c9c-81a1-fcbea2200222
-- title:
--   Det Inv: ker b C eq range al C and ker al C eq range b C
-- statement:
--   The Det Inv construction uses the ker b C eq range al C and ker al C eq range b C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SandwichKernelRangeExact.lean#L10-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SandwichKernelRangeExact.lean#L10-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsBasisOfBot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerMapSubsetImMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SandwichDatumScalarAction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FontaineAinfLocalDomainXiAdicOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SandwichKernelRangeExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
open GlobalTheory GlobalTheory.DetInv

theorem GlobalTheory.DetInv.ker_bC_eq_range_alC_and_ker_alC_eq_range_bC : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Γ : Type) [CommRing Γ] [Algebra ℤ_[p] Γ] (h : ℕ) (D : Datum ε h Γ), LinearMap.ker (bC C D) = LinearMap.range (alC C D) ∧ LinearMap.ker (alC C D) = LinearMap.range (bC C D) := by sorry
