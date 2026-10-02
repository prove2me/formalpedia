-- Prove2me | Theorems.Thm_LeblSCV_Holomorphic_holomorphic_comp
-- name    : LeblSCV.Holomorphic.holomorphic_comp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T02:14:46.943036+00:00
-- url     : https://prove2.me/theorems/1fdf5631-030d-4a25-a840-8b9a1b963245
-- title:
--   Theorem 1.3.5 — composition of holomorphic mappings is holomorphic
-- statement:
--   Let $U \subset \mathbb{C}^n$ and $V \subset \mathbb{C}^m$ be open sets, and suppose $f : U \to V$ and $g : V \to \mathbb{C}^q$ are both holomorphic mappings (each component holomorphic in the sense of Definition 1.1.2). Then the composition
--   $$g \circ f : U \to \mathbb{C}^q$$
--   is holomorphic.
--
--   **Formalization Note.** $f$ and $g$ are functions on all of `Fin n → ℂ` and `Fin m → ℂ`; "$f : U \to V$" is `Set.MapsTo f U V`, and holomorphy of mappings is Definition 1.3.4 (`IsHolomorphicMapOn`).
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 29, Theorem 1.3.5

import Mathlib
import Definitions.Def_LeblSCV_Holomorphic_IsHolomorphicMapOn

namespace LeblSCV.Holomorphic

/-- Theorem 1.3.5 (Lebl, p. 29). Let `U ⊆ ℂⁿ` and `V ⊆ ℂᵐ` be open, and let `f : U → V` and
`g : V → ℂ^q` be holomorphic mappings (Definition 1.3.4). Then `g ∘ f` is holomorphic on `U`. -/
theorem holomorphic_comp {n m q : ℕ} {U : Set (Fin n → ℂ)} {V : Set (Fin m → ℂ)}
    (hU : IsOpen U) (hV : IsOpen V)
    {f : (Fin n → ℂ) → (Fin m → ℂ)} {g : (Fin m → ℂ) → (Fin q → ℂ)}
    (hfUV : Set.MapsTo f U V) (hf : IsHolomorphicMapOn f U) (hg : IsHolomorphicMapOn g V) :
    IsHolomorphicMapOn (g ∘ f) U := by sorry

end LeblSCV.Holomorphic
