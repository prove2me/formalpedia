-- Prove2me | Theorems.Thm_LeblSCV_Holomorphic_det_real_jacobian
-- name    : LeblSCV.Holomorphic.det_real_jacobian
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T02:15:22.038983+00:00
-- url     : https://prove2.me/theorems/44786aa6-0710-488d-8426-fe904fdd6125
-- title:
--   Proposition 1.3.7 — $|\det Df(p)|^2 = \det D_{\mathbb{R}} f(p)$
-- statement:
--   Let $U \subset \mathbb{C}^n$ be open, $p \in U$, and $f : U \to \mathbb{C}^n$ holomorphic. Let $Df(p) = \left[\frac{\partial f_k}{\partial z_\ell}(p)\right]_{k\ell}$ be the holomorphic Jacobian matrix and $D_{\mathbb{R}} f(p)$ the real Jacobian, the $2n \times 2n$ real matrix of the derivative of $f$ at $p$ when $\mathbb{C}^n$ is identified with $\mathbb{R}^{2n}$. Then
--   $$|\det Df(p)|^2 = \det D_{\mathbb{R}} f(p).$$
--   In particular holomorphic mappings preserve orientation.
--
--   **Formalization Note.** The entries of $Df(p)$ are Wirtinger derivatives (`wirtinger`). $\det D_{\mathbb{R}} f(p)$ is `LinearMap.det` of the real Fréchet derivative `fderiv ℝ f p` as a real-linear endomorphism of `Fin n → ℂ`; the determinant of an endomorphism does not depend on the basis, so it equals the determinant of the real Jacobian matrix in the coordinates $(x_1, y_1, \dots, x_n, y_n)$ used on both source and target. Holomorphy is Definition 1.3.4.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 31, Proposition 1.3.7

import Mathlib
import Definitions.Def_LeblSCV_Holomorphic_IsHolomorphicMapOn
import Definitions.Def_LeblSCV_Holomorphic_wirtinger

namespace LeblSCV.Holomorphic

/-- Proposition 1.3.7 (Lebl, p. 31). Let `U ⊆ ℂⁿ` be open, `p ∈ U`, and `f : U → ℂⁿ` holomorphic.
Then `|det Df(p)|² = det D_ℝ f(p)`, where `Df(p) = [∂f_k/∂z_ℓ (p)]_{kℓ}` is the holomorphic
Jacobian matrix (Wirtinger derivatives) and `D_ℝ f(p)` is the real Jacobian of `f` viewed as a map
of `ℝ^{2n}`, i.e. the real derivative of `f` at `p`, whose determinant is basis-independent. -/
theorem det_real_jacobian {n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {f : (Fin n → ℂ) → (Fin n → ℂ)} (hf : IsHolomorphicMapOn f U) {p : Fin n → ℂ} (hp : p ∈ U) :
    ‖(Matrix.of fun (k l : Fin n) => wirtinger l (fun z => f z k) p).det‖ ^ 2 =
      LinearMap.det ((fderiv ℝ f p : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) :
        (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ)) := by sorry

end LeblSCV.Holomorphic
