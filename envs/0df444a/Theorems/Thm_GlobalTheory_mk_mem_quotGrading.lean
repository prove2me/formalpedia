-- Prove2me | Theorems.Thm_GlobalTheory_mk_mem_quotGrading
-- name    : GlobalTheory.mk_mem_quotGrading
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:11.177606+00:00
-- url     : https://prove2.me/theorems/30b5c7a1-d7f6-494e-859f-6287c168d8d8
-- title:
--   Global Theory: mk mem quot Grading
-- statement:
--   The Global Theory construction uses the mk mem quot Grading property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L18-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_AwayLiftCompFromZeroRingHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)

theorem GlobalTheory.mk_mem_quotGrading (I : Ideal A) {d : ℕ} {a : A} (ha : a ∈ 𝒜 d) :
    Ideal.Quotient.mk I a ∈ quotGrading 𝒜 I d := by sorry
