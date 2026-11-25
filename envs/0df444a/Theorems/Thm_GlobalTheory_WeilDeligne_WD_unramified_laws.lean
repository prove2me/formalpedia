-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_WD_unramified_laws
-- name    : GlobalTheory.WeilDeligne.WD.unramified_laws
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T16:59:15.066173+00:00
-- url     : https://prove2.me/theorems/bb4263e6-7c6d-4183-8d26-f14d341588b6
-- title:
--   WD: unramified laws
-- statement:
--   The WD construction uses the unramified laws property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsEquivOfMapEq.lean#L246-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsEquivOfMapEq.lean#L246-L267

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsEquivOfMapEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
open GlobalTheory.WeilDeligne.WD
open Unram
variable (h)

theorem GlobalTheory.WeilDeligne.WD.unramified_laws :
    (∀ m : Multiset ℂ, (0 : ℂ) ∉ m → unr (lpUnr h m) ∧ frobEig (lpUnr h m) = m ∧
      lpDim (lpUnr h m) = Multiset.card m) ∧
    (∀ a b : WD h, unr (lpSum a b) ↔ unr a ∧ unr b) ∧
    (∀ (a : WD h) (s : ℝ), unr (lpTw a s) ↔ unr a) ∧
    (∀ a χ : WD h, lpDim χ = 1 → unr a → unr χ → unr (lpChar a χ)) ∧
    (∀ a b : WD h, unr a → unr b → frobEig (lpSum a b) = frobEig a + frobEig b) ∧
    (∀ (a : WD h) (s : ℝ), unr a →
      frobEig (lpTw a s) = (frobEig a).map (· * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ))) ∧
    (∀ (a χ : WD h) (c : ℂ), unr a → unr χ → lpDim χ = 1 → frobEig χ = {c} →
      frobEig (lpChar a χ) = (frobEig a).map (· * c)) ∧
    unr (lpZero h) ∧
    frobEig (lpZero h) = 0 ∧
    (∀ a : WD h, unr a → a = lpUnr h (frobEig a)) ∧
    (∀ a : WD h, unr a → mono0 a) ∧
    (∀ a : WD h, unr a → (0 : ℂ) ∉ frobEig a) ∧
    (∀ a : WD h, unr a → Multiset.card (frobEig a) = lpDim a) ∧
    (∀ a : WD h, unr a → (tempered a ↔ ∀ α ∈ frobEig a, ‖α‖ = 1)) ∧
    (∀ a : WD h, unr a ↔ mono0 a ∧ ∀ σ ∈ Ine (F := E) A, inePol a σ = (X - 1) ^ lpDim a) := by sorry
