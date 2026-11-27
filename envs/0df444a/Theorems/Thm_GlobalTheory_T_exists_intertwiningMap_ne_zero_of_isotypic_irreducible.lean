-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_intertwiningMap_ne_zero_of_isotypic_irreducible
-- name    : GlobalTheory.T.exists_intertwiningMap_ne_zero_of_isotypic_irreducible
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:36:43.846196+00:00
-- url     : https://prove2.me/theorems/59203db6-ee79-566e-bbdd-400c8ac50595
-- title:
--   T: exists intertwining Map ne zero of isotypic irreducible
-- statement:
--   The T construction uses the exists intertwining Map ne zero of isotypic irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntertwiningMapNeZeroOfIsotypicIrreducibleStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntertwiningMapNeZeroOfIsotypicIrreducibleStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntertwiningMapNeZeroOfIsotypicIrreducible
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntertwiningMapNeZeroOfIsotypicIrreducibleStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_intertwiningMap_ne_zero_of_isotypic_irreducible : ∀ (H V W : Type) [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H V) (σ : Representation ℂ H W), σ.IsIrreducible → (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) = ⊤ → (∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (σ' : Representation ℂ H W'), σ'.IsIrreducible → ∀ f' : σ'.IntertwiningMap ρ, f' ≠ 0 → Nonempty (σ.Equiv σ')) → ∀ v : V, v ≠ 0 → ∃ p : ρ.IntertwiningMap σ, p v ≠ 0 := by sorry
