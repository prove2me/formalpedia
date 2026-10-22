-- Prove2me | Theorems.Thm_JHolomorphic_HasWeakPartialsOn_integral_contDiff_one
-- name    : JHolomorphic.HasWeakPartialsOn.integral_contDiff_one
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T12:49:00.545792+00:00
-- url     : https://prove2.me/theorems/ec20421d-d46f-4fd1-ae7c-07d51b6f5b78
-- title:
--   Weak partial derivatives on a planar domain can be tested against $C^1$ functions
-- statement:
--   Let $E$ be a finite-dimensional real normed space and let $U\subseteq\mathbb{C}$ be open. Suppose $u_s,u_t:\mathbb{C}\to E$ are weak partial derivatives of $u:\mathbb{C}\to E$ on $U$, i.e. $\int(\partial_s\varphi)\,u=-\int\varphi\,u_s$ and $\int(\partial_t\varphi)\,u=-\int\varphi\,u_t$ for every real $C^\infty$ function $\varphi$ with compact support in $U$, and suppose $u,u_s,u_t$ are integrable on every compact subset of $U$. Then the same two identities hold for every real $C^1$ function $\varphi$ with compact support in $U$.
--
--   This lets weak partial derivatives be tested against $C^1$ functions, for instance products of a test function with a $C^1$ coefficient.
--
--   **Formalization Note** The hypothesis is `HasWeakPartialsOn U u us ut` together with `IntegrableOn` of `u`, `us`, `ut` on every compact `K ⊆ U`. For the test function: `ContDiff ℝ 1 φ`, `HasCompactSupport φ`, `tsupport φ ⊆ U`; $\partial_s\varphi(z)$ is `fderiv ℝ φ z 1` and $\partial_t\varphi(z)$ is `fderiv ℝ φ z Complex.I`. The integrals are Bochner integrals over $\mathbb{C}$.
-- source:
--   Standard (distribution theory).

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory

/-- If `uₛ`, `uₜ` are weak partial derivatives of `u` on an open set `U ⊆ ℂ` and `u`, `uₛ`, `uₜ`
are integrable on every compact subset of `U`, then the defining identities
`∫ (∂ₛφ) u = -∫ φ uₛ` and `∫ (∂ₜφ) u = -∫ φ uₜ` also hold for every real `C¹` function `φ` with
compact support in `U`. -/
theorem HasWeakPartialsOn.integral_contDiff_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {u us ut : ℂ → E}
    (h : HasWeakPartialsOn U u us ut)
    (hint : ∀ K ⊆ U, IsCompact K →
      IntegrableOn u K ∧ IntegrableOn us K ∧ IntegrableOn ut K)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (∫ z, fderiv ℝ φ z 1 • u z = -∫ z, φ z • us z) ∧
      (∫ z, fderiv ℝ φ z Complex.I • u z = -∫ z, φ z • ut z) := by
  sorry

end JHolomorphic
