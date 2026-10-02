-- Prove2me | Theorems.Thm_LeblSCV_BallPolydisc_jacobian_ne_zero_of_injOn
-- name    : LeblSCV.BallPolydisc.jacobian_ne_zero_of_injOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T02:25:43.297985+00:00
-- url     : https://prove2.me/theorems/99cdc9b8-6a8b-40b0-9949-1b9727154294
-- title:
--   Theorem 1.6.6 — an injective holomorphic map has nonvanishing Jacobian and is biholomorphic onto its image
-- statement:
--   Let $U \subset \mathbb{C}^n$ be open and $f : U \to \mathbb{C}^n$ holomorphic and one-to-one. Then the Jacobian determinant
--   $$J_f(z) = \det Df(z) = \det\Big[ \frac{\partial f_k}{\partial z_\ell}(z) \Big]_{k\ell}$$
--   is never zero on $U$. In particular, if a holomorphic map $f : U \to V$ is one-to-one and onto for two open sets $U, V \subset \mathbb{C}^n$, then $f$ is biholomorphic.
--
--   The statement fails for smooth real maps ($x \mapsto x^3$ on $\mathbb{R}$), and fails when the dimensions of source and target differ.
--
--   **Formalization Note.** $\mathbb{C}^n$ is `Fin n → ℂ`; holomorphic is `DifferentiableOn ℂ f U`, one-to-one is `Set.InjOn f U`. $\det Df(z)$ is `LinearMap.det` of the complex Fréchet derivative `fderiv ℂ f z`. "One-to-one and onto $V$" is `Set.BijOn f U V`, and biholomorphic is `IsBiholomorphicMap f U V` (Definition 1.4.1, with a holomorphic inverse on $V$).
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 43, Theorem 1.6.6

import Mathlib
import Definitions.Def_LeblSCV_BallPolydisc_IsBiholomorphicMap

namespace LeblSCV.BallPolydisc

/-- Theorem 1.6.6 (Lebl, p. 43). If `U ⊆ ℂⁿ` is open and `f : U → ℂⁿ` is holomorphic and
one-to-one, then the Jacobian determinant `det Df(z)` is never zero on `U`; in particular, if
`f` maps `U` one-to-one onto an open set `V ⊆ ℂⁿ`, then `f : U → V` is biholomorphic. -/
theorem jacobian_ne_zero_of_injOn {n : ℕ} (U : Set (Fin n → ℂ)) (hU : IsOpen U)
    (f : (Fin n → ℂ) → (Fin n → ℂ)) (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U) :
    (∀ z ∈ U, LinearMap.det (fderiv ℂ f z : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0) ∧
      ∀ V : Set (Fin n → ℂ), IsOpen V → Set.BijOn f U V → IsBiholomorphicMap f U V := by sorry

end LeblSCV.BallPolydisc
