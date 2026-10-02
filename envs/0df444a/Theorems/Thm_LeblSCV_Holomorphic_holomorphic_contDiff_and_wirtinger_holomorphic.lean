-- Prove2me | Theorems.Thm_LeblSCV_Holomorphic_holomorphic_contDiff_and_wirtinger_holomorphic
-- name    : LeblSCV.Holomorphic.holomorphic_contDiff_and_wirtinger_holomorphic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T02:02:33.218395+00:00
-- url     : https://prove2.me/theorems/b2e44fb4-df48-44c1-b511-5618e515a852
-- title:
--   Proposition 1.1.3 — holomorphic functions are $C^\infty$ and $\partial f/\partial z_k$ is holomorphic
-- statement:
--   Let $U \subset \mathbb{C}^n$ be an open set and let $f : U \to \mathbb{C}$ be holomorphic, i.e. locally bounded and complex-differentiable in each variable separately (Definition 1.1.2). Then $f$ is infinitely (real) differentiable on $U$, and for every $k = 1, \dots, n$ the Wirtinger derivative
--   $$\frac{\partial f}{\partial z_k} = \frac{1}{2}\left(\frac{\partial f}{\partial x_k} - i\frac{\partial f}{\partial y_k}\right)$$
--   is again holomorphic on $U$.
--
--   This is the first step from the separate, one-variable-at-a-time definition of holomorphy to joint regularity; it makes the Cauchy–Riemann description of holomorphic functions equivalent to Definition 1.1.2.
--
--   **Formalization Note.** "Infinitely differentiable" is `ContDiffOn ℝ ∞ f U` with `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)` ($C^\infty$, not real-analytic), where `Fin n → ℂ` is regarded as a real vector space. Holomorphy is the book's Definition 1.1.2 (`IsHolomorphicOn`), not Mathlib's `DifferentiableOn ℂ`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 15, Proposition 1.1.3

import Mathlib
import Definitions.Def_LeblSCV_Holomorphic_IsHolomorphicOn
import Definitions.Def_LeblSCV_Holomorphic_wirtinger

open scoped ContDiff

namespace LeblSCV.Holomorphic

/-- Proposition 1.1.3 (Lebl, p. 15). A holomorphic function (Definition 1.1.2) on an open set
`U ⊆ ℂⁿ` is infinitely (real) differentiable, and each Wirtinger derivative `∂f/∂z_k` is again
holomorphic on `U`. -/
theorem holomorphic_contDiff_and_wirtinger_holomorphic {n : ℕ} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) {f : (Fin n → ℂ) → ℂ} (hf : IsHolomorphicOn f U) :
    ContDiffOn ℝ ∞ f U ∧ ∀ k : Fin n, IsHolomorphicOn (wirtinger k f) U := by sorry

end LeblSCV.Holomorphic
