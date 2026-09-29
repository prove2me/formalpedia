-- Prove2me | Theorems.Thm_MakeToStockRM_ExpDensity_whitening_normal_iff_conormal
-- name    : MakeToStockRM.ExpDensity.whitening_normal_iff_conormal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:37:57.435934+00:00
-- url     : https://prove2.me/theorems/2b0e7d1c-21f4-4b9a-86ac-7afae7e9118d
-- title:
--   Preamble of Proposition 2: $T\vec v$ normal to $\partial\Omega^*$ iff $\vec v\parallel\Sigma\vec n$
-- statement:
--   Let $\sigma>0$, $\delta>0$, $-1<\varrho<1$ and let $\Sigma=\begin{pmatrix}\sigma^2&\sigma\delta\varrho\\ \sigma\delta\varrho&\delta^2\end{pmatrix}$ be the covariance matrix of $(\mathcal X,\mathcal Y)$. As in the paper, let $V$ be a rotation matrix ($VV'=I$, $\det V=1$) whose rows are orthonormal eigenvectors of $\Sigma$, and $E=\operatorname{diag}(e_1,e_2)$ with $e_1,e_2>0$ the corresponding eigenvalues, so that $\Sigma=V'EV$. Let $T=E^{-1/2}V$ be the whitening map. Then:
--
--   1. For all $v,w\in\mathbb R^2$, $\;(Tv)\cdot(Tw)=v\cdot(\Sigma^{-1}w)$.
--   2. For every nonzero $n\in\mathbb R^2$ and every $v\in\mathbb R^2$,
--   $$
--   \bigl(\forall w\in\mathbb R^2,\ n\cdot w=0\ \Rightarrow\ (Tv)\cdot(Tw)=0\bigr)\iff \exists c\in\mathbb R,\ v=c\,\Sigma n .
--   $$
--
--   Since $T$ maps the tangent directions of $\partial\Omega$ (those orthogonal to its normal $n$) onto the tangent directions of $\partial\Omega^*=\partial(T\Omega)$, part 2 says that the hypothesis of Proposition 2, "$T\vec v$ is normal to $\partial\Omega^*$", holds at a boundary point exactly when the reflection direction $\vec v$ is parallel to the conormal $\Sigma\vec n$. This is how the mission pins down the reflection field in the goal theorem.
--
--   **Formalization Note** The eigenvalue condition $e_i>0$ is automatic for a positive definite $\Sigma$ and is stated as a hypothesis alongside the decomposition $\Sigma=V'EV$; $E^{-1/2}$ is $\operatorname{diag}(1/\sqrt{e_i})$. Vectors are `Fin 2 → ℝ`, inventory first.
-- source:
--   Caldentey, Wein, Revenue Management of a Make-to-Stock Queue, Oper. Res. 54(5), 2006, p. 867, preamble of Proposition 2 (definition of V, E, T = E^{-1/2}V, Ω* = T(Ω)) and its hypothesis "T v⃗ is normal to ∂Ω*"

import Mathlib
import Definitions.Def_MakeToStockRM_ExpDensity_covMatrix

namespace MakeToStockRM.ExpDensity

open Matrix

theorem whitening_normal_iff_conormal (σ δ ϱ : ℝ) (hσ : 0 < σ) (hδ : 0 < δ) (hϱ : |ϱ| < 1)
    (V : Matrix (Fin 2) (Fin 2) ℝ) (e : Fin 2 → ℝ)
    (hV : V * V.transpose = 1) (hVdet : V.det = 1) (he : ∀ i, 0 < e i)
    (hSigma : covMatrix σ δ ϱ = V.transpose * Matrix.diagonal e * V) :
    (∀ v w : Fin 2 → ℝ,
      ((Matrix.diagonal (fun i => (Real.sqrt (e i))⁻¹) * V) *ᵥ v)
          ⬝ᵥ ((Matrix.diagonal (fun i => (Real.sqrt (e i))⁻¹) * V) *ᵥ w)
        = v ⬝ᵥ ((covMatrix σ δ ϱ)⁻¹ *ᵥ w)) ∧
    (∀ n v : Fin 2 → ℝ, n ≠ 0 →
      ((∀ w : Fin 2 → ℝ, n ⬝ᵥ w = 0 →
          ((Matrix.diagonal (fun i => (Real.sqrt (e i))⁻¹) * V) *ᵥ v)
            ⬝ᵥ ((Matrix.diagonal (fun i => (Real.sqrt (e i))⁻¹) * V) *ᵥ w) = 0)
        ↔ ∃ c : ℝ, v = c • (covMatrix σ δ ϱ *ᵥ n))) := by sorry

end MakeToStockRM.ExpDensity
