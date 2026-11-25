-- Prove2me | Theorems.Thm_GlobalTheory_twistedTrace_equivariant_and_injective_of_groupDet
-- name    : GlobalTheory.twistedTrace_equivariant_and_injective_of_groupDet
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:51:22.848123+00:00
-- url     : https://prove2.me/theorems/99cda7b4-c353-5048-918c-7a97f980f9ba
-- title:
--   Global Theory: twisted Trace equivariant and injective of group Det
-- statement:
--   The Global Theory construction uses the twisted Trace equivariant and injective of group Det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TwistedTraceEquivariantAndInjectiveOfGroupDet.lean#L19-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TwistedTraceEquivariantAndInjectiveOfGroupDet.lean#L19-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwistedTraceEquivariantAndInjectiveOfGroupDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Matrix
open Polynomial
open GlobalTheory

theorem GlobalTheory.twistedTrace_equivariant_and_injective_of_groupDet :
    ∀ (H K R : Type) [Group H] [Fintype H] [DecidableEq H] [Field K] [CommRing R] [Algebra K R] (st : H → R →ₐ[K] R), (∀ x, st 1 x = x) → (∀ h h' x, st (h * h') x = st h' (st h x)) → ∀ (χ : H →* Kˣ) (u : R), (Matrix.of fun h g : H => st (h * g) u).det ∈ nonZeroDivisors R → (∀ (F : R) (g : H), st g (∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h F) = ((χ g : Kˣ) : K) • ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h F) ∧ (∀ f : R, (∀ h, ∑ g, (((χ g)⁻¹ : Kˣ) : K) • st g (f * st h u) = 0) → f = 0) ∧ (∀ F : H → R, (∀ h g, st g (F h) = ((χ g : Kˣ) : K) • F h) → ∑ h, F h * st h u = 0 → F = 0) := by sorry
