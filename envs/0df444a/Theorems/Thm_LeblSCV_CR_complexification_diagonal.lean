-- Prove2me | Theorems.Thm_LeblSCV_CR_complexification_diagonal
-- name    : LeblSCV.CR.complexification_diagonal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T07:51:29.686179+00:00
-- url     : https://prove2.me/theorems/47a2667a-b2c4-40f5-a32c-174e3204a014
-- title:
--   Proposition 3.1.5 — complexification of a real-analytic function on a domain of $\mathbb{C}^n$
-- statement:
--   Let $U \subset \mathbb{C}^n$ be a domain and $f : U \to \mathbb{C}$ real-analytic (in the real coordinates of $\mathbb{C}^n \cong \mathbb{R}^{2n}$). Then there exist a domain $V \subset \mathbb{C}^n \times \mathbb{C}^n$ such that
--   $$\{ (z, \zeta) : \zeta = \bar z \text{ and } z \in U \} \subset V,$$
--   and a unique holomorphic function $F : V \to \mathbb{C}$ with $F(z, \bar z) = f(z)$ for all $z \in U$ (the book writes $f(z, \bar z)$ for $f(z)$). Uniqueness is for the found $V$: any holomorphic $G$ on $V$ with $G(z, \bar z) = f(z)$ on $U$ equals $F$ on $V$. This makes precise the idea of treating $z$ and $\bar z$ as independent variables.
--
--   **Formalization Note.** Real-analytic is `IsRealAnalyticOn U f` for `f : (Fin n → ℂ) → ℂ` over `ℝ`; holomorphic is `DifferentiableOn ℂ` on `(Fin n → ℂ) × (Fin n → ℂ)`; $\bar z$ is the coordinatewise conjugate; a domain is `IsOpen ∧ IsConnected`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 107, Proposition 3.1.5

import Mathlib
import Definitions.Def_LeblSCV_CR_IsRealAnalyticOn

open ComplexConjugate

namespace LeblSCV.CR

/-- Proposition 3.1.5 (Complexification part II; Lebl, p. 107): if `U ⊂ ℂⁿ` is a domain and
`f : U → ℂ` is real-analytic (in the real coordinates of `ℂⁿ ≅ ℝ^{2n}`), then there is a domain
`V ⊂ ℂⁿ × ℂⁿ` with `{(z, ζ) : ζ = z̄, z ∈ U} ⊂ V` and a unique holomorphic `F : V → ℂ` with
`F(z, z̄) = f(z)` for all `z ∈ U` (the book writes `f(z, z̄)` for `f(z)`). -/
theorem complexification_diagonal {n : ℕ} (U : Set (Fin n → ℂ)) (hU : IsOpen U)
    (hUc : IsConnected U) (f : (Fin n → ℂ) → ℂ) (hf : IsRealAnalyticOn U f) :
    ∃ V : Set ((Fin n → ℂ) × (Fin n → ℂ)), IsOpen V ∧ IsConnected V ∧
      {x : (Fin n → ℂ) × (Fin n → ℂ) | x.2 = (fun k => conj (x.1 k)) ∧ x.1 ∈ U} ⊆ V ∧
      ∃ F : (Fin n → ℂ) × (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F V ∧
        (∀ z ∈ U, F (z, fun k => conj (z k)) = f z) ∧
        ∀ G : (Fin n → ℂ) × (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G V →
          (∀ z ∈ U, G (z, fun k => conj (z k)) = f z) → Set.EqOn G F V := by sorry

end LeblSCV.CR
