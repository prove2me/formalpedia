-- Prove2me | Theorems.Thm_GlobalTheory_SylvesterInertia_nonpos_of_mem
-- name    : GlobalTheory.SylvesterInertia.nonpos_of_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:23:31.893878+00:00
-- url     : https://prove2.me/theorems/5357b28b-cf3a-4647-a91c-31788d693213
-- title:
--   Sylvester Inertia: nonpos of mem
-- statement:
--   The Sylvester Inertia construction uses the nonpos of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSignatureFstUniqueSylvester.lean#L80-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSignatureFstUniqueSylvester.lean#L80-L86

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

theorem GlobalTheory.SylvesterInertia.nonpos_of_mem {a b : ℕ} {J : Matrix n n ℂ} {e : n ≃ Fin a ⊕ Fin b} {P : GL (Fin a ⊕ Fin b) ℂ}
    (h : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) * J.reindex e e *
      (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) = Formalism.UG.Jpq a b)
    {x : n → ℂ} (hx : x ∈ LinearMap.range (chg e P ∘ₗ inrMap a b)) : qf J x ≤ 0 := by sorry
