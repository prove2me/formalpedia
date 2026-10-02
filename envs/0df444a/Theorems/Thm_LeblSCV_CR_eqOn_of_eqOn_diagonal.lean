-- Prove2me | Theorems.Thm_LeblSCV_CR_eqOn_of_eqOn_diagonal
-- name    : LeblSCV.CR.eqOn_of_eqOn_diagonal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T07:42:58.420562+00:00
-- url     : https://prove2.me/theorems/abf5a8e6-7c5c-4a42-9d72-1fb99c0d7691
-- title:
--   Lemma 3.1.4 — holomorphic functions agreeing on the diagonal $\zeta = \bar z$ agree
-- statement:
--   Let $V \subset \mathbb{C}^n \times \mathbb{C}^n$ be a domain, with coordinates $(z, \zeta) \in \mathbb{C}^n \times \mathbb{C}^n$, let
--   $$D = \{ (z, \zeta) \in \mathbb{C}^n \times \mathbb{C}^n : \zeta = \bar z \},$$
--   and suppose $D \cap V \neq \emptyset$. If $f, g : V \to \mathbb{C}$ are holomorphic and $f = g$ on $D \cap V$, then $f = g$ on all of $V$. The set $D$ is called the diagonal; it is a totally real submanifold of real dimension $2n$ in $\mathbb{C}^{2n}$.
--
--   **Formalization Note.** $\mathbb{C}^n \times \mathbb{C}^n$ is `(Fin n → ℂ) × (Fin n → ℂ)`, holomorphic is `DifferentiableOn ℂ` on this product, $\bar z$ is the coordinatewise complex conjugate, and a domain is `IsOpen ∧ IsConnected`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 106, Lemma 3.1.4

import Mathlib

open ComplexConjugate

namespace LeblSCV.CR

/-- Lemma 3.1.4 (Lebl, p. 106): let `V ⊂ ℂⁿ × ℂⁿ` be a domain, with coordinates `(z, ζ)`, let
`D = {(z, ζ) : ζ = z̄}` and suppose `D ∩ V ≠ ∅`. If `f, g` are holomorphic on `V` and `f = g` on
`D ∩ V`, then `f = g` on all of `V`. -/
theorem eqOn_of_eqOn_diagonal {n : ℕ} (V : Set ((Fin n → ℂ) × (Fin n → ℂ))) (hV : IsOpen V)
    (hVc : IsConnected V)
    (hDV : ({x | x.2 = fun k => conj (x.1 k)} ∩ V).Nonempty)
    (f g : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (hf : DifferentiableOn ℂ f V)
    (hg : DifferentiableOn ℂ g V)
    (hfg : ∀ x ∈ {x : (Fin n → ℂ) × (Fin n → ℂ) | x.2 = fun k => conj (x.1 k)} ∩ V,
      f x = g x) :
    Set.EqOn f g V := by sorry

end LeblSCV.CR
