-- Prove2me | Theorems.Thm_GlobalTheory_finite_of_isHausdorff_of_finite_quotient
-- name    : GlobalTheory.finite_of_isHausdorff_of_finite_quotient
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:50:14.804103+00:00
-- url     : https://prove2.me/theorems/1b06f70d-eeef-505d-b13d-f10717fc303b
-- title:
--   Global Theory: finite of is Hausdorff of finite quotient
-- statement:
--   The Global Theory construction uses the finite of is Hausdorff of finite quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L12-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimeEqBotOrMaximalIdealOfIsFieldAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing TensorProduct

theorem GlobalTheory.finite_of_isHausdorff_of_finite_quotient {R : Type*} [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] (M : Type*) [AddCommGroup M] [Module R M] [IsHausdorff I M]
    [Module.Finite R (M ⧸ (I • ⊤ : Submodule R M))] : Module.Finite R M := by sorry
