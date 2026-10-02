-- Prove2me | Theorems.Thm_LeblSCV_Levi_levi_inertia_biholomorphic_invariant
-- name    : LeblSCV.Levi.levi_inertia_biholomorphic_invariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T03:24:13.567141+00:00
-- url     : https://prove2.me/theorems/5cf3f375-d30e-46a1-92d9-715c9232d275
-- title:
--   Theorem 2.3.8 — the inertia of the Levi form is a biholomorphic invariant
-- statement:
--   Let $U, U' \subset \mathbb{C}^n$ be open sets with smooth boundary, $p \in \partial U$, $q \in \partial U'$, $V$ and $V'$ open neighbourhoods of $p$ and $q$, and $f : V \to V'$ a biholomorphic map with $f(p) = q$ and
--   $$f(U \cap V) = U' \cap V'.$$
--   Then, for any defining functions of $U$ at $p$ and of $U'$ at $q$, the Levi form of $U$ at $p$ and the Levi form of $U'$ at $q$ have the same numbers of positive and of negative eigenvalues. In particular $U$ is pseudoconvex at $p$ if and only if $U'$ is pseudoconvex at $q$, and $U$ is strongly pseudoconvex at $p$ if and only if $U'$ is strongly pseudoconvex at $q$.
--
--   **Formalization Note.** Neighbourhoods are taken open; `IsBiholomorphicOn f V V'` is a holomorphic bijection $V \to V'$ with holomorphic inverse.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 72, Theorem 2.3.8

import Mathlib
import Definitions.Def_LeblSCV_Levi_HasSmoothBoundary
import Definitions.Def_LeblSCV_Levi_leviPosIndex
import Definitions.Def_LeblSCV_Levi_IsPseudoconvexAt
import Definitions.Def_LeblSCV_Levi_IsBiholomorphicOn

namespace LeblSCV.Levi

/-- Theorem 2.3.8 (Lebl, p. 72): a local biholomorphism `f : V → V'` with `f(p) = q` and
`f(U ∩ V) = U' ∩ V'` preserves the inertia of the Levi form (for any defining functions at `p`
and `q`), hence pseudoconvexity and strong pseudoconvexity. -/
theorem levi_inertia_biholomorphic_invariant {n : ℕ} (U U' : Set (Fin n → ℂ))
    (hU : HasSmoothBoundary U) (hU' : HasSmoothBoundary U')
    (p q : Fin n → ℂ) (hp : p ∈ frontier U) (hq : q ∈ frontier U')
    (V V' : Set (Fin n → ℂ)) (hV : IsOpen V) (hpV : p ∈ V) (hV' : IsOpen V') (hqV' : q ∈ V')
    (f : (Fin n → ℂ) → (Fin n → ℂ)) (hf : IsBiholomorphicOn f V V') (hfp : f p = q)
    (hfU : f '' (U ∩ V) = U' ∩ V') :
    (∀ (W : Set (Fin n → ℂ)) (r : (Fin n → ℂ) → ℝ) (W' : Set (Fin n → ℂ))
        (r' : (Fin n → ℂ) → ℝ), IsDefiningFunction U p W r → IsDefiningFunction U' q W' r' →
        leviPosIndex r p = leviPosIndex r' q ∧ leviNegIndex r p = leviNegIndex r' q) ∧
      (IsPseudoconvexAt U p ↔ IsPseudoconvexAt U' q) ∧
      (IsStronglyPseudoconvexAt U p ↔ IsStronglyPseudoconvexAt U' q) := by sorry

end LeblSCV.Levi
