-- Prove2me | Theorems.Thm_GlobalTheory_InvariantSupremum_eq_bot_or_eq_top_of_invariant
-- name    : GlobalTheory.InvariantSupremum.eq_bot_or_eq_top_of_invariant
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:19:55.411873+00:00
-- url     : https://prove2.me/theorems/9cc2670c-c27f-4506-a963-4e5b5549516c
-- title:
--   Invariant Supremum: eq bot or eq top of invariant
-- statement:
--   The Invariant Supremum construction uses the eq bot or eq top of invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqBotOrEqTopOfInvariant.lean#L5-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqBotOrEqTopOfInvariant.lean#L5-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqBotOrEqTopOfInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InvariantSupremum

theorem GlobalTheory.InvariantSupremum.eq_bot_or_eq_top_of_invariant {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G W) (hσ : Representation.IsIrreducible σ) (P : Submodule ℂ W)
    (hP : ∀ g : G, ∀ w ∈ P, σ g w ∈ P) : P = ⊥ ∨ P = ⊤ := by sorry
