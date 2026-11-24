-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Radical_unipotent_radical_basic
-- name    : GlobalTheory.RootEx.Radical.unipotent_radical_basic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:49.661609+00:00
-- url     : https://prove2.me/theorems/a790f528-39b9-4c26-bd5f-fddd95e5ce2c
-- title:
--   Radical: unipotent radical basic
-- statement:
--   The Radical construction uses the unipotent radical basic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnipotentRadicalBasic.lean#L217-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnipotentRadicalBasic.lean#L217-L225

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem GlobalTheory.RootEx.Radical.unipotent_radical_basic : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), (∀ g : GL (n ⊕ Fin c) k, g ∈ N k n c p ↔ InN p g) ∧ (∀ g ∈ N k n c p, ∀ h ∈ N k n c p, simpleSum (g * h) = simpleSum g + simpleSum h) ∧ (∀ g ∈ N k n c p, Matrix.GeneralLinearGroup.det g = 1) ∧ (∀ (x : GL n k), ∀ g ∈ N k n c p, embX c x * g * (embX c x)⁻¹ ∈ N k n c p ∧ simpleSum (embX c x * g * (embX c x)⁻¹) = simpleSum g) ∧ (∀ r ∈ R k n c p, ∃! xg : GL n k × N k n c p, r = embX c xg.1 * (xg.2 : GL (n ⊕ Fin c) k)) ∧ (∀ (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k), (∀ r s, lev p s ≤ lev p r → M r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) → M.det = 1) ∧ (∀ (l : ℕ) (u : n → k), l < p → rowE c l u ∈ N k n c p ∧ simpleSum (rowE c l u) = 0) ∧ ∀ (i : ℕ) (β : n → k), p < i → colE c i β ∈ N k n c p ∧ simpleSum (colE c i β) = 0 := by sorry
