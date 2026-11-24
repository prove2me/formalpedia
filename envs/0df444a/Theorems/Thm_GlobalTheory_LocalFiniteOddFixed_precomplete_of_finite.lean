-- Prove2me | Theorems.Thm_GlobalTheory_LocalFiniteOddFixed_precomplete_of_finite
-- name    : GlobalTheory.LocalFiniteOddFixed.precomplete_of_finite
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:14:14.972058+00:00
-- url     : https://prove2.me/theorems/0701702a-4ac9-45b7-bccd-b5e2911fb9b7
-- title:
--   Local Finite Odd Fixed: precomplete of finite
-- statement:
--   The Local Finite Odd Fixed construction uses the precomplete of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfFinite.lean#L10-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfFinite.lean#L10-L26

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

theorem GlobalTheory.LocalFiniteOddFixed.precomplete_of_finite (O : Type) [CommRing O] (I : Ideal O) [IsPrecomplete I O]
    (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] : IsPrecomplete I M := by sorry
