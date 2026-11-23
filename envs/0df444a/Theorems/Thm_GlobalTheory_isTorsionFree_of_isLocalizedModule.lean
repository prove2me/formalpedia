-- Prove2me | Theorems.Thm_GlobalTheory_isTorsionFree_of_isLocalizedModule
-- name    : GlobalTheory.isTorsionFree_of_isLocalizedModule
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:56:09.269801+00:00
-- url     : https://prove2.me/theorems/bb27a8bf-bab5-4f0a-8643-222c758bf2db
-- title:
--   Global Theory: is Torsion Free of is Localized Module
-- statement:
--   The Global Theory construction uses the is Torsion Free of is Localized Module property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L199-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L199-L202

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
omit [IsNoetherianRing A] [IsIntegrallyClosed A]

theorem GlobalTheory.isTorsionFree_of_isLocalizedModule (f : M →ₗ[A] V) [IsLocalizedModule A⁰ f] :
    Module.IsTorsionFree A V := by sorry
