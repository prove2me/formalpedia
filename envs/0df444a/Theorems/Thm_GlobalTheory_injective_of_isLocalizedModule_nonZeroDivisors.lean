-- Prove2me | Theorems.Thm_GlobalTheory_injective_of_isLocalizedModule_nonZeroDivisors
-- name    : GlobalTheory.injective_of_isLocalizedModule_nonZeroDivisors
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:56:02.621071+00:00
-- url     : https://prove2.me/theorems/538e076e-0a29-40c3-a680-5a772b07ab62
-- title:
--   Global Theory: injective of is Localized Module non Zero Divisors
-- statement:
--   The Global Theory construction uses the injective of is Localized Module non Zero Divisors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L206-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L206-L209

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
variable [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
variable {V : Type*} [AddCommGroup V] [Module A V]
omit [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]

theorem GlobalTheory.injective_of_isLocalizedModule_nonZeroDivisors [Module.IsTorsionFree A M]
    (f : M →ₗ[A] V) [IsLocalizedModule A⁰ f] : Function.Injective f := by sorry
