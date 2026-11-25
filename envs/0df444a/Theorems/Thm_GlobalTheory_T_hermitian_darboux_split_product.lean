-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitian_darboux_split_product
-- name    : GlobalTheory.T.hermitian_darboux_split_product
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:50.862812+00:00
-- url     : https://prove2.me/theorems/97d38641-f386-4073-9c7a-ba0398835b9a
-- title:
--   T: hermitian darboux split product
-- statement:
--   The T construction uses the hermitian darboux split product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/HermitianDarbouxSplitProductStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/HermitianDarbouxSplitProductStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_HermitianDarbouxSplitProduct
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_FiniteNonunitMatrix
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_HermitianDarbouxSplitProductStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hermitian_darboux_split_product : ∀ (k : Type) [Field k] [CharZero k] (R S E₁ E₂ : Type) [CommRing R] [CommRing S] [Algebra R S] [CommRing E₁] [IsArtinianRing E₁] [Algebra k E₁] [CommRing E₂] (c : S →ₐ[R] S) (c₁ : E₁ →ₐ[k] E₁) (c₂ : E₂ →+* E₂) (ξ₁ : E₁) (s : S ≃+* E₁ × E₂), IsUnit ξ₁ → c₁ ξ₁ = -ξ₁ → (∀ x, c₁ (c₁ x) = x) → (∀ x, (s (c x)).1 = c₁ (s x).1) → (∀ x, (s (c x)).2 = c₂ (s x).2) → ∀ (β : Type) [Fintype β] [DecidableEq β] (J : Matrix β β S), IsUnit J.det → ∀ lam : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J) →* ℂˣ, (∀ (p : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) (t : GL β S), (∀ i j, (s ((((p : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S) - 1) i j)).2 = 0) → (∀ i j, (s (((t : Matrix β β S) - 1) i j)).2 = 0) → ((p : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S) * GlobalTheory.WeilM.diagCols β = GlobalTheory.WeilM.diagCols β * (t : Matrix β β S) → lam p = 1) → ∀ g : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J), (∀ i j, (s ((((g : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S) - 1) i j)).2 = 0) → lam g = 1 := by sorry
