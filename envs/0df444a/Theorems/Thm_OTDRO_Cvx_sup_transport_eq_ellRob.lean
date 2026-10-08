-- Prove2me | Theorems.Thm_OTDRO_Cvx_sup_transport_eq_ellRob
-- name    : OTDRO.Cvx.sup_transport_eq_ellRob
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:18.246982+00:00
-- url     : https://prove2.me/theorems/4ef00d75-0a6e-4065-aa2d-d38891d54202
-- title:
--   (25), p. 32 — sup_Δ {ℓ(βᵀ(x+Δ)) − λ'(ΔᵀA(x)Δ − δ)} = ℓ_rob(β, λ; x) with λ' = λ/√δ
-- statement:
--   Let $x \in \mathbb{R}^d$ be such that $A(x)$ is positive definite, let $\ell : \mathbb{R} \to \mathbb{R}$ be any function, $\delta > 0$, $\beta \in \mathbb{R}^d$ and $\lambda \ge 0$. Then
--   $$\sup_{\Delta \in \mathbb{R}^d} \Big\{ \ell\big(\beta^{\mathsf T}(x + \Delta)\big) - \frac{\lambda}{\sqrt{\delta}}\big(\Delta^{\mathsf T}A(x)\Delta - \delta\big) \Big\} = \sup_{\gamma \in \mathbb{R}} F(\gamma, \beta, \lambda; x) = \ell_{rob}(\beta, \lambda; x),$$
--   as extended real numbers.
--
--   This is display (25): it rewrites the inner supremum of the transport dual over the perturbation $\Delta \in \mathbb{R}^d$ as a one-dimensional supremum over $\gamma$. The proof of Lemma 2 (convexity of $\ell_{rob}$) starts from the left-hand side, which is visibly a supremum of functions convex in $(\beta, \lambda)$ when $\ell$ is convex.
--
--   **Formalization Note** On the page the multiplier on the left of (25) is the dual variable before the change of variables "from $\lambda\sqrt{\delta}$ to $\lambda$"; here it is written explicitly as $\lambda/\sqrt{\delta}$, so that one symbol $\lambda$ is not used for two different multipliers. The identity holds for every $\beta$, including $\beta = 0$, where both sides equal $\ell(0) + \lambda\sqrt{\delta}$. The same identity is also drafted in mission 1 of this series (`OTDRO.Dual.sup_transport_eq_ellRob`), because draft items of parallel missions cannot import each other.
-- source:
--   arXiv:1810.02403v3, §5.1, proof of Theorem 1, display (25), p. 32

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting

namespace OTDRO.Cvx

open Matrix

/-- Display (25), p. 32: for positive definite `A(x)`, `δ > 0` and `λ ≥ 0`,
`sup_Δ {ℓ(βᵀ(x + Δ)) − λ'(ΔᵀA(x)Δ − δ)} = sup_γ F(γ, β, λ; x) = ℓ_rob(β, λ; x)`, where the
transport multiplier on the left is the *old* dual variable `λ' = λ / √δ` (the page's change of
variables "from `λ√δ` to `λ`"). Valid for every `β`, including `β = 0`. -/
theorem sup_transport_eq_ellRob {d : ℕ}
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hQ : (A x).PosDef)
    (ℓ : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) (hlam : 0 ≤ lam) :
    (⨆ Δ : EuclideanSpace ℝ (Fin d),
      ((ℓ (inner ℝ β (x + Δ)) - (lam / Real.sqrt δ) *
        (dotProduct Δ.ofLp (A x *ᵥ Δ.ofLp) - δ) : ℝ) : EReal)) =
      OTDRO.Dual.ellRob ℓ A δ β lam x := by sorry

end OTDRO.Cvx
