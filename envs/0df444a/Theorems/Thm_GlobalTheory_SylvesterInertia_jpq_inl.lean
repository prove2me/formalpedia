-- Prove2me | Theorems.Thm_GlobalTheory_SylvesterInertia_jpq_inl
-- name    : GlobalTheory.SylvesterInertia.jpq_inl
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:23:34.833028+00:00
-- url     : https://prove2.me/theorems/f98b788f-93d4-4e03-ac9c-be3810d021f2
-- title:
--   Sylvester Inertia: jpq inl
-- statement:
--   The Sylvester Inertia construction uses the jpq inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSignatureFstUniqueSylvester.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSignatureFstUniqueSylvester.lean#L63-L65

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSignatureFstUniqueSylvester
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SylvesterInertia
open Matrix Module
open scoped ComplexOrder
variable {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.SylvesterInertia.jpq_inl (a b : ℕ) (z : Fin a → ℂ) :
    star (inlMap a b z) ⬝ᵥ Formalism.UG.Jpq a b *ᵥ inlMap a b z = star z ⬝ᵥ z := by sorry
