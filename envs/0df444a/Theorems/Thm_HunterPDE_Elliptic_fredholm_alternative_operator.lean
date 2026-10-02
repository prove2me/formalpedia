-- Prove2me | Theorems.Thm_HunterPDE_Elliptic_fredholm_alternative_operator
-- name    : HunterPDE.Elliptic.fredholm_alternative_operator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:52:14.094285+00:00
-- url     : https://prove2.me/theorems/4f4f93de-be4c-495f-be6e-e8360b67946b
-- title:
--   Theorem 4.50 — Fredholm alternative for Fredholm operators of index zero
-- statement:
--   Let $\mathcal{H}$ be a Hilbert space and $T \in \mathcal{L}(\mathcal{H})$ a Fredholm operator with $\operatorname{ind} T = 0$. Then one of the following two alternatives holds:
--
--   1. $\ker T^* = 0$, $\ker T = 0$, $\operatorname{ran} T = \mathcal{H}$ and $\operatorname{ran} T^* = \mathcal{H}$;
--   2. $\ker T^* \ne 0$; $\ker T$ and $\ker T^*$ are finite-dimensional with the same dimension; $\operatorname{ran} T = (\ker T^*)^\perp$ and $\operatorname{ran} T^* = (\ker T)^\perp$.
--
--   $$\text{(2)}\quad \dim\ker T = \dim\ker T^* < \infty, \qquad \operatorname{ran} T = (\ker T^*)^\perp, \qquad \operatorname{ran} T^* = (\ker T)^\perp .$$
--
--   The equation $Tx = y$ thus behaves like a square linear system: solvable for all $y$ exactly when solutions are unique, and otherwise solvable iff $y$ satisfies finitely many orthogonality conditions.
--
--   **Formalization Note.** Scalars are any `RCLike` field; $T^*$ is `ContinuousLinearMap.adjoint T`; kernels and ranges are submodules, and $(\cdot)^\perp$ is the orthogonal complement. The notes give no proof ("For proofs, see …", §4.B.2).
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 124, Theorem 4.50

import Mathlib
import Definitions.Def_HunterPDE_Elliptic_Fredholm

namespace HunterPDE.Elliptic

/-- Theorem 4.50 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 124: let `T ∈ ℒ(ℋ)` be a
Fredholm operator on a Hilbert space with `ind T = 0`. Then one of two alternatives holds:
(1) `ker T* = 0`, `ker T = 0`, `ran T = ℋ`, `ran T* = ℋ`;
(2) `ker T* ≠ 0`; `ker T` and `ker T*` are finite-dimensional with the same dimension;
`ran T = (ker T*)^⊥` and `ran T* = (ker T)^⊥`.
`T*` is the Hilbert-space adjoint `ContinuousLinearMap.adjoint T`. -/
theorem fredholm_alternative_operator {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (T : H →L[𝕜] H) (hT : IsFredholm T)
    (hind : index T = 0) :
    (LinearMap.ker (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H) = ⊥ ∧
      LinearMap.ker (T : H →ₗ[𝕜] H) = ⊥ ∧
      LinearMap.range (T : H →ₗ[𝕜] H) = ⊤ ∧
      LinearMap.range (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H) = ⊤) ∨
    (LinearMap.ker (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H) ≠ ⊥ ∧
      FiniteDimensional 𝕜 (LinearMap.ker (T : H →ₗ[𝕜] H)) ∧
      FiniteDimensional 𝕜 (LinearMap.ker (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H)) ∧
      Module.finrank 𝕜 (LinearMap.ker (T : H →ₗ[𝕜] H)) =
        Module.finrank 𝕜 (LinearMap.ker (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H)) ∧
      LinearMap.range (T : H →ₗ[𝕜] H) =
        (LinearMap.ker (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H))ᗮ ∧
      LinearMap.range (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H) =
        (LinearMap.ker (T : H →ₗ[𝕜] H))ᗮ) := by sorry

end HunterPDE.Elliptic
