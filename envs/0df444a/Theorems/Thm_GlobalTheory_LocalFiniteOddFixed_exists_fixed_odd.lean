-- Prove2me | Theorems.Thm_GlobalTheory_LocalFiniteOddFixed_exists_fixed_odd
-- name    : GlobalTheory.LocalFiniteOddFixed.exists_fixed_odd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:14:14.750848+00:00
-- url     : https://prove2.me/theorems/e24592c7-43c1-458b-a3fe-7c7ebd265a76
-- title:
--   Local Finite Odd Fixed: exists fixed odd
-- statement:
--   The Local Finite Odd Fixed construction uses the exists fixed odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfFinite.lean#L197-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfFinite.lean#L197-L302

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
open GlobalTheory.UnitLemma

theorem GlobalTheory.LocalFiniteOddFixed.exists_fixed_odd (K : UQ) (L : Type) [Field L] [Algebra K.E L] [Algebra K.O L]
    [IsScalarTower K.O K.E L] [Module.Finite K.E L] (τ : L →+* L) (hτ : ∀ x, τ (τ x) = x)
    (hc : ∀ e : K.E, τ (algebraMap K.E L e) = algebraMap K.E L (K.c e)) :
    ∃ y : L, y ≠ 0 ∧ τ y = y ∧ K.eta (Algebra.norm K.E y) = -1 := by sorry
