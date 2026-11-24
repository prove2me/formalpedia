-- Prove2me | Theorems.Thm_GlobalTheory_HeisVacuum_mem_span_translates_vacuum
-- name    : GlobalTheory.HeisVacuum.mem_span_translates_vacuum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:19:11.293795+00:00
-- url     : https://prove2.me/theorems/bc4e6224-52d5-4af5-b15d-c20dab7dcd70
-- title:
--   Heis Vacuum: mem span translates vacuum
-- statement:
--   The Heis Vacuum construction uses the mem span translates vacuum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSpanHeisenbergTranslatesOfVacuum.lean#L7-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSpanHeisenbergTranslatesOfVacuum.lean#L7-L193

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSpanHeisenbergTranslatesOfVacuum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.HeisVacuum

theorem GlobalTheory.HeisVacuum.mem_span_translates_vacuum (X M : Type) [AddCommGroup X] [AddCommGroup M] [Module ℂ M]
    (β : X → X → ℂ) (ρ : X → M →ₗ[ℂ] M) (Λ : AddSubgroup X) (e : M)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hd : ∀ x, β x x = 1) (h0 : ∀ v, ρ 0 v = v)
    (hρ : ∀ x y v, ρ x (ρ y v) = β x y • ρ (x + y) v)
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ a ∈ Λ, β x a ^ 2 = 1)
    (hdiv : ∀ N : ℕ, 0 < N → ∀ x : X, ∃ y : X, N • y = x)
    (hfin : ∀ N : ℕ, 0 < N → ∃ R : Set X, R.Finite ∧ ∀ t ∈ Λ, ∃ r ∈ R, ∃ u ∈ Λ, t = r + N • u)
    (he : e ≠ 0) (hε : ∀ u ∈ Λ, ∃ ε : ℂ, ρ u e = ε • e) (h2 : ∀ u ∈ Λ, ρ (2 • u) e = e)
    (hvac : ∀ v : M, (∀ u ∈ Λ, ∀ ε : ℂ, ρ u e = ε • e → ρ u v = ε • v) → ∃ c : ℂ, v = c • e)
    (v : M) (hv : ∃ N : ℕ, 0 < N ∧ ∀ u ∈ Λ, ρ (N • u) v = v) :
    v ∈ Submodule.span ℂ (Set.range fun x => ρ x e) := by sorry
