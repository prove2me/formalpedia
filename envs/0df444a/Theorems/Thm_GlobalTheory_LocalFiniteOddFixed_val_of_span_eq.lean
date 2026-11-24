-- Prove2me | Theorems.Thm_GlobalTheory_LocalFiniteOddFixed_val_of_span_eq
-- name    : GlobalTheory.LocalFiniteOddFixed.val_of_span_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:14:22.59326+00:00
-- url     : https://prove2.me/theorems/e7a44db2-0ee7-4081-89fb-bcd0c633497b
-- title:
--   Local Finite Odd Fixed: val of span eq
-- statement:
--   The Local Finite Odd Fixed construction uses the val of span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfFinite.lean#L170-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfFinite.lean#L170-L185

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

theorem GlobalTheory.LocalFiniteOddFixed.val_of_span_eq (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type}
    [Field E] [Algebra O E] [IsFractionRing O E] (x : O) (n : ℕ)
    (h : Ideal.span {x} = IsLocalRing.maximalIdeal O ^ n) : val O (algebraMap O E x) = n := by sorry
