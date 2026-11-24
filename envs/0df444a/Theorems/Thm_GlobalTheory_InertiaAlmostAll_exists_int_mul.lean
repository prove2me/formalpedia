-- Prove2me | Theorems.Thm_GlobalTheory_InertiaAlmostAll_exists_int_mul
-- name    : GlobalTheory.InertiaAlmostAll.exists_int_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:23:28.580723+00:00
-- url     : https://prove2.me/theorems/054f3216-0841-4f90-93ba-4ff55d6c8e20
-- title:
--   Inertia Almost All: exists int mul
-- statement:
--   The Inertia Almost All construction uses the exists int mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinitePlacesInertiaNotFixingFiniteExtension.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinitePlacesInertiaNotFixingFiniteExtension.lean#L15-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinitePlacesInertiaNotFixingFiniteExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.InertiaAlmostAll

theorem GlobalTheory.InertiaAlmostAll.exists_int_mul (F : Type) {Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (y : Ω) : ∃ c : ℤ, c ≠ 0 ∧ IsIntegral ℤ ((c : Ω) * y) := by sorry
