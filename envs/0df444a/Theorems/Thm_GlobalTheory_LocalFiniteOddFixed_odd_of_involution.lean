-- Prove2me | Theorems.Thm_GlobalTheory_LocalFiniteOddFixed_odd_of_involution
-- name    : GlobalTheory.LocalFiniteOddFixed.odd_of_involution
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:14:09.676329+00:00
-- url     : https://prove2.me/theorems/b735a980-e9ea-4946-a325-1825a58eaa27
-- title:
--   Local Finite Odd Fixed: odd of involution
-- statement:
--   The Local Finite Odd Fixed construction uses the odd of involution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfFinite.lean#L99-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfFinite.lean#L99-L166

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.LocalFiniteOddFixed

theorem GlobalTheory.LocalFiniteOddFixed.odd_of_involution (k : Type) [Field k] [Finite k] (τ : k →+* k) (hτ : ∀ x, τ (τ x) = x)
    (q f : ℕ) (hc : Nat.card k = (q ^ 2) ^ f) (a : k) (ha : a ^ (q ^ 2) = a) (hta : τ a ≠ a) :
    Odd f := by sorry
