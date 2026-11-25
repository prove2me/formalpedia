-- Prove2me | Theorems.Thm_GlobalTheory_InertiaLift_exists_smul_eq
-- name    : GlobalTheory.InertiaLift.exists_smul_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:19:36.145104+00:00
-- url     : https://prove2.me/theorems/676d9765-891a-49b2-bb31-fe333d6d852c
-- title:
--   Inertia Lift: exists smul eq
-- statement:
--   The Inertia Lift construction uses the exists smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteGaloisInertiaLiftsAbsoluteInertiaRat.lean#L33-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteGaloisInertiaLiftsAbsoluteInertiaRat.lean#L33-L55

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

theorem GlobalTheory.InertiaLift.exists_smul_eq {A A' : ValuationSubring Ω}
    (h : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω x) < 1 ↔ A'.valuation (algebraMap F Ω x) < 1) :
    ∃ g : Ω ≃ₐ[F] Ω, ∀ y, A'.valuation (g y) < 1 ↔ A.valuation y < 1 := by sorry
