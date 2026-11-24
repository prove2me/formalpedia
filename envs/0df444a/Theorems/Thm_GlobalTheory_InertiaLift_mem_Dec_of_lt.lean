-- Prove2me | Theorems.Thm_GlobalTheory_InertiaLift_mem_Dec_of_lt
-- name    : GlobalTheory.InertiaLift.mem_Dec_of_lt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:19:37.85896+00:00
-- url     : https://prove2.me/theorems/e9124374-1c06-4d01-adf6-96a320f0d4d4
-- title:
--   Inertia Lift: mem Dec of lt
-- statement:
--   The Inertia Lift construction uses the mem Dec of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteGaloisInertiaLiftsAbsoluteInertiaRat.lean#L106-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteGaloisInertiaLiftsAbsoluteInertiaRat.lean#L106-L118

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
omit [IsAlgClosure F Ω]

theorem GlobalTheory.InertiaLift.mem_Dec_of_lt {A : ValuationSubring Ω} {σ : G F Ω}
    (h : ∀ y, A.valuation (σ y) < 1 ↔ A.valuation y < 1) : σ ∈ Dec (F := F) A := by sorry
