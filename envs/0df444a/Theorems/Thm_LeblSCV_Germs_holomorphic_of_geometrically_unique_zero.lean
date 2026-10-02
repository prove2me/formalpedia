-- Prove2me | Theorems.Thm_LeblSCV_Germs_holomorphic_of_geometrically_unique_zero
-- name    : LeblSCV.Germs.holomorphic_of_geometrically_unique_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:09:36.719261+00:00
-- url     : https://prove2.me/theorems/f802fac1-c141-4f92-9f92-230388bdf187
-- title:
--   Proposition 6.3.1 — a geometrically unique zero depends holomorphically on parameters
-- statement:
--   Let $U' \subset \mathbb{C}^{n-1}$ and $D \subset \mathbb{C}$ be domains (connected open sets), and let $f \in \mathcal{O}(U' \times D)$. Suppose that for each fixed $z' \in U'$ the function $z_n \mapsto f(z', z_n)$ has a **geometrically unique** zero $\alpha(z') \in D$, that is, $\alpha(z')$ is its only zero in $D$ (its multiplicity may exceed one). Then
--   $$ \alpha : U' \to \mathbb{C} \text{ is holomorphic in } U'. $$
--
--   The holomorphic implicit function theorem gives this when $\partial f / \partial z_n \neq 0$; here no condition on the derivative is imposed, only the uniqueness of the zero. Nothing like this holds for real-analytic or smooth functions ($x^2 - y^3 = 0$ has the unique real solution $y = x^{2/3}$).
--
--   **Formalization Note.** $\mathbb{C}^{n-1}$ is `Fin d → ℂ`; domains are `IsOpen ∧ IsConnected`; holomorphic is `DifferentiableOn ℂ`. The hypothesis says: for each $z' \in U'$, $\alpha(z') \in D$, $f(z', \alpha(z')) = 0$, and every $w \in D$ with $f(z', w) = 0$ equals $\alpha(z')$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 176, Proposition 6.3.1

import Mathlib

namespace LeblSCV.Germs

/-- Proposition 6.3.1 (Lebl, p. 176). `ℂ^{n-1}` is `Fin d → ℂ` with `d = n - 1`. Let
`U' ⊆ ℂ^{n-1}` and `D ⊆ ℂ` be domains (connected open sets) and `f ∈ 𝒪(U' × D)`. Suppose that for
each `z' ∈ U'` the function `z_n ↦ f(z', z_n)` has a geometrically unique zero `α(z') ∈ D`, i.e.
`α(z')` is its only zero in `D`. Then `α` is holomorphic in `U'`. -/
theorem holomorphic_of_geometrically_unique_zero {d : ℕ} (U' : Set (Fin d → ℂ)) (D : Set ℂ)
    (hU'o : IsOpen U') (hU'c : IsConnected U') (hDo : IsOpen D) (hDc : IsConnected D)
    (f : (Fin d → ℂ) × ℂ → ℂ) (hf : DifferentiableOn ℂ f (U' ×ˢ D))
    (α : (Fin d → ℂ) → ℂ)
    (hα : ∀ z' ∈ U', α z' ∈ D ∧ f (z', α z') = 0 ∧ ∀ w ∈ D, f (z', w) = 0 → w = α z') :
    DifferentiableOn ℂ α U' := by sorry

end LeblSCV.Germs
