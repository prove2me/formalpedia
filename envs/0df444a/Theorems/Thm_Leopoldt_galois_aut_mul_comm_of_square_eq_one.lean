-- Prove2me | Theorems.Thm_Leopoldt_galois_aut_mul_comm_of_square_eq_one
-- name    : Leopoldt.galois_aut_mul_comm_of_square_eq_one
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:23:59.333988+00:00
-- url     : https://prove2.me/theorems/ff0d76c5-1bd3-4c51-86bb-2e7bd0bb81cf
-- title:
--   Galois automorphisms commute if every automorphism is an involution
-- statement:
--   Let $K/\mathbb Q$ be a finite Galois extension. If every Galois automorphism has square equal to the identity, then any two automorphisms commute:
--   $$\sigma\tau=\tau\sigma\qquad(\sigma,\tau\in\operatorname{Gal}(K/\mathbb Q)).$$
--
--   This elementary group fact supplies the abelian branch of the exponent-two case split for a totally real Galois field. It applies to the Galois group without requiring an explicit classification of multiquadratic extensions.
-- source:
--   Standard elementary group identity: a group of exponent two is abelian; applied to the exponent-two branch of Leopoldt.galois_totallyReal_injection_of_three_le_finrank.

import Definitions.Def_LeopoldtDefect
import Mathlib.Tactic.Group

open NumberField

namespace Leopoldt
theorem galois_aut_mul_comm_of_square_eq_one
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (h : ∀ σ : K ≃ₐ[ℚ] K, σ * σ = 1)
    (σ τ : K ≃ₐ[ℚ] K) : σ * τ = τ * σ := by sorry
end Leopoldt
