-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_RT_CellSplit_char_trivial_first
-- name    : GlobalTheory.CompanionTheory.Ar.RT.CellSplit.char_trivial_first
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:20:52.661218+00:00
-- url     : https://prove2.me/theorems/778b9d5f-1955-4a5b-9dab-8989eac98e12
-- title:
--   Cell Split: char trivial first
-- statement:
--   The Cell Split construction uses the char trivial first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/HermitianDarbouxSplitProduct.lean#L163-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/HermitianDarbouxSplitProduct.lean#L163-L206

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_FiniteNonunitMatrix
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_HermitianDarbouxSplitProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.RT GlobalTheory.CompanionTheory.Ar.RT.CellSplit
open GlobalTheory.WeilM

theorem GlobalTheory.CompanionTheory.Ar.RT.CellSplit.char_trivial_first : ∀ (k : Type) [Field k] [CharZero k] (R S E₁ E₂ : Type) [CommRing R] [CommRing S] [Algebra R S] [CommRing E₁] [IsArtinianRing E₁] [Algebra k E₁] [CommRing E₂] (c : S →ₐ[R] S) (c₁ : E₁ →ₐ[k] E₁) (c₂ : E₂ →+* E₂) (ξ₁ : E₁) (s : S ≃+* E₁ × E₂), IsUnit ξ₁ → c₁ ξ₁ = -ξ₁ → (∀ x, c₁ (c₁ x) = x) → (∀ x, (s (c x)).1 = c₁ (s x).1) → (∀ x, (s (c x)).2 = c₂ (s x).2) → ∀ (β : Type) [Fintype β] [DecidableEq β] (J : Matrix β β S), IsUnit J.det → ∀ lam : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J) →* ℂˣ, (∀ (p : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) (t : GL β S), (∀ i j, (s ((((p : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S) - 1) i j)).2 = 0) → (∀ i j, (s (((t : Matrix β β S) - 1) i j)).2 = 0) → ((p : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S) * GlobalTheory.WeilM.diagCols β = GlobalTheory.WeilM.diagCols β * (t : Matrix β β S) → lam p = 1) → ∀ g : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J), (∀ i j, (s ((((g : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S) - 1) i j)).2 = 0) → lam g = 1 := by sorry
