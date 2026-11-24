-- Prove2me | Theorems.Thm_GlobalTheory_InertiaLift_mem_Ine_of_integral
-- name    : GlobalTheory.InertiaLift.mem_Ine_of_integral
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:19:47.801939+00:00
-- url     : https://prove2.me/theorems/72582d36-ce79-40ac-a04f-bb6340fc4651
-- title:
--   Inertia Lift: mem Ine of integral
-- statement:
--   The Inertia Lift construction uses the mem Ine of integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteGaloisInertiaLiftsAbsoluteInertiaRat.lean#L12-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteGaloisInertiaLiftsAbsoluteInertiaRat.lean#L12-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteGaloisInertiaLiftsAbsoluteInertiaRat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField Pointwise
open GlobalTheory GlobalTheory.InertiaLift
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem GlobalTheory.InertiaLift.mem_Ine_of_integral {A : ValuationSubring Ω} {σ : G F Ω} (hσ : σ ∈ Dec (F := F) A)
    (h : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b) < 1) : σ ∈ Ine (F := F) A := by sorry
