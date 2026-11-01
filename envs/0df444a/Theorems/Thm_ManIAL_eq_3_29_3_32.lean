-- Prove2me | Theorems.Thm_ManIAL_eq_3_29_3_32
-- name    : ManIAL.eq_3_29_3_32
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:13:10.010987+00:00
-- url     : https://prove2.me/theorems/e6d81562-cb09-425e-9d7e-e9907eec34bb
-- title:
--   Displays (3.29)–(3.32) — multiplier, stationarity and feasibility residuals (corrected: $\nabla f-\mathcal A^*\bar z$ in (3.30))
-- statement:
--   Let $h$ be convex and $\ell_h$-Lipschitz, $\sigma_k>0$, $z^k\in\mathbb R^m$, let $f$ be differentiable at $x^{k+1}$, let $y^{k+1}=\operatorname{prox}_{h/\sigma_k}(\mathcal Ax^{k+1}-z^k/\sigma_k)$ and $\bar z^{k+1}=z^k-\sigma_k(\mathcal Ax^{k+1}-y^{k+1})$. Then, for any $\mathcal M\subseteq\mathbb R^n$ and $\psi_k=\mathcal L_{\sigma_k}(\cdot,z^k)$:
--
--   1. (3.29) and (3.30), second line: $-\bar z^{k+1}\in\partial h(y^{k+1})$, so $\operatorname{dist}(-\bar z^{k+1},\partial h(y^{k+1}))=0$;
--   2. (3.30), first line:
--   $$
--   P_{T_{x^{k+1}}\mathcal M}\big(\nabla f(x^{k+1})-\mathcal A^*\bar z^{k+1}\big)=\operatorname{grad}\psi_k(x^{k+1}),
--   $$
--   so the inexactness criterion (3.12) gives $\|P_{T_{x^{k+1}}\mathcal M}(\nabla f(x^{k+1})-\mathcal A^*\bar z^{k+1})\|\le\epsilon_k$;
--   3. (3.32): $\|\mathcal Ax^{k+1}-y^{k+1}\|\le(\ell_h+\|z^k\|)/\sigma_k$, and hence $\le(\ell_h+z_{\max})/\sigma_k$ whenever $\|z^k\|\le z_{\max}$.
--
--   These are the three KKT residuals of the triple $(x^{k+1},y^{k+1},\bar z^{k+1})$ after one outer iteration.
--
--   Differences from the source:
--   - correction: (3.30) ‖P_{T_{x^{k+1}}M}(∇f(x^{k+1}) + A*z̄^{k+1})‖ ≤ ϵ_k → P_{T_{x^{k+1}}M}(∇f(x^{k+1}) − A*z̄^{k+1}) = grad ψ_k(x^{k+1}); reason: by (3.15) and (3.27) the gradient of ψ_k is ∇f − A*z̄, the sign of Definition 3.1; counterexample to the printed sign: n = m = 2, A = I, M = S¹, f(x) = −x₂, h(y) = ⟨(0,1), y⟩, σ_k = 1, z^k = 0, x^{k+1} = (1,0): grad ψ_k(x^{k+1}) = 0 but ‖P(∇f + A*z̄)‖ = 2
--   - generalization: (3.30) as inequalities derived from (3.28) and (3.29) → −z̄^{k+1} ∈ ∂h(y^{k+1}) and the identity with grad ψ_k(x^{k+1}); reason: membership gives dist = 0, and the identity with (3.12) gives the bound ≤ ϵ_k
--   - generalization: the iterates of Algorithm 1 on the manifold M, for all k ≥ 1 → any set M, any σ_k > 0, z^k, x^{k+1} with f differentiable there; reason: contains every iterate; (3.32)'s last step is stated for any bound z_max on ‖z^k‖ (display (3.31) supplies one)
--   - encoding: dist(−z, ∂h(y)) ≤ ϵ → ∃ g ∈ ∂h(y), ‖z + g‖ ≤ ϵ; reason: ∂h(y) is nonempty and compact for real-valued convex h, so the distance is attained
-- source:
--   Deng, Hu, Wu & Wen, Oracle complexities of augmented Lagrangian methods for nonsmooth manifold optimization, arXiv:2404.05121v2, displays (3.29)–(3.32), p.12

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ZORiem_RGD_rgrad
import Definitions.Def_SAGA_StronglyConvex_IsProxPoint
import Definitions.Def_KallMayerSLP_KKT_subdifferential
import Definitions.Def_ManIAL_psi
import Definitions.Def_ManIAL_zbar

open ProjLikeRetr.Retractor ZORiem.RGD SAGA.StronglyConvex

namespace ManIAL

/-- **Displays (3.29)–(3.32)** (Deng–Hu–Wu–Wen, arXiv:2404.05121v2, p.12), with the sign of
(3.30) corrected. Let `h` be convex and `ℓ_h`-Lipschitz, `σ_k > 0`, `z^k ∈ ℝᵐ`, `f`
differentiable at `x^{k+1}`, `y^{k+1} = prox_{h/σ_k}(Ax^{k+1} − z^k/σ_k)` and
`z̄^{k+1} = z^k − σ_k(Ax^{k+1} − y^{k+1})`. Then
1. (3.29), (3.30) second line: `−z̄^{k+1} ∈ ∂h(y^{k+1})`, so `dist(−z̄^{k+1}, ∂h(y^{k+1})) = 0`;
2. (3.30) first line: `P_{T_{x^{k+1}}M}(∇f(x^{k+1}) − A*z̄^{k+1}) = grad ψ_k(x^{k+1})`, so
   (3.12) gives `‖P_{T_{x^{k+1}}M}(∇f(x^{k+1}) − A*z̄^{k+1})‖ ≤ ϵ_k`;
3. (3.32): `‖Ax^{k+1} − y^{k+1}‖ ≤ (ℓ_h + ‖z^k‖)/σ_k`, hence `≤ (ℓ_h + z_max)/σ_k` for any
   bound `z_max` on `‖z^k‖`.

**Formalization Note.** (3.30) and (3.33) print `∇f + A*z̄`; with (3.15) and (3.27) the
gradient is `∇f − A*z̄`, the sign of Definition 3.1. Item 2 is stated as the identity behind the
inequality, for any set `M`. In (3.32) `z_max` is any bound on `‖z^k‖`; display (3.31)
(`eq_3_31`) supplies `z_max = (β₀π²/6)‖Ax⁰ − y⁰‖` for the iterates. -/
theorem eq_3_29_3_32 {n m : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (ℓh : ℝ) (hℓh : 0 ≤ ℓh) (hh : ConvexOn ℝ Set.univ h)
    (hhL : ∀ y y', |h y - h y'| ≤ ℓh * ‖y - y'‖)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (σk : ℝ) (hσk : 0 < σk) (zk : EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) (hfx : DifferentiableAt ℝ f x)
    (y : EuclideanSpace ℝ (Fin m)) (hy : IsProxPoint h (1 / σk) (A x - σk⁻¹ • zk) y) :
    -zbar σk zk A x y ∈ KallMayerSLP.KKT.subdifferential h y ∧
    (tangentSpace M x).starProjection
        (gradient f x - ContinuousLinearMap.adjoint A (zbar σk zk A x y)) =
      rgrad M (psi f h A σk zk) x ∧
    ‖A x - y‖ ≤ (ℓh + ‖zk‖) / σk ∧
    ∀ zmax : ℝ, ‖zk‖ ≤ zmax → ‖A x - y‖ ≤ (ℓh + zmax) / σk := by sorry

end ManIAL
