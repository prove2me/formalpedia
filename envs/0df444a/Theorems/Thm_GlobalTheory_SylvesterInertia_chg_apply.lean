-- Prove2me | Theorems.Thm_GlobalTheory_SylvesterInertia_chg_apply
-- name    : GlobalTheory.SylvesterInertia.chg_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:30.981618+00:00
-- url     : https://prove2.me/theorems/e2423b53-730d-41b8-83e1-8d54d753ad2e
-- title:
--   Sylvester Inertia: chg apply
-- statement:
--   The Sylvester Inertia construction uses the chg apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSignatureFstUniqueSylvester.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSignatureFstUniqueSylvester.lean#L33-L34

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

theorem GlobalTheory.SylvesterInertia.chg_apply {a b : ℕ} (e : n ≃ Fin a ⊕ Fin b) (P : GL (Fin a ⊕ Fin b) ℂ) (y : Fin a ⊕ Fin b → ℂ) :
    chg e P y = ((P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) *ᵥ y) ∘ e := by sorry
