-- Prove2me | Theorems.Thm_OTDRO_WorstCase_ellRob_lambda_derivatives
-- name    : OTDRO.WorstCase.ellRob_lambda_derivatives
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:05:23.763612+00:00
-- url     : https://prove2.me/theorems/eb7d8545-654a-40ad-9754-9ab25d64c827
-- title:
--   Proposition 2 (a) and λ-part of (b), (12c)–(12d), p. 16 — one-sided λ-derivatives of ℓ_rob are min/max of −√δ(γ²βᵀA(x)⁻¹β − 1) over Γ*
-- statement:
--   Assume Assumption 1, $\delta>0$, $B\subseteq\mathbb R^d$ convex, and let $\ell$ satisfy Assumption 2 and be of the form $\ell(u)=\max_{i=1,\dots,K}\ell_i(u)$ for a positive integer $K$ and continuously differentiable $\ell_i:\mathbb R\to\mathbb R$. Let $\mathbb U_1=\{(\beta,\lambda):\beta\in B,\ \lambda>\lambda_{thr}(\beta)\}$ and, for $\gamma\in\mathbb R$,
--   $$\partial_\lambda F(\gamma,\beta,\lambda;x)=-\sqrt\delta\bigl(\gamma^2\beta^{\mathsf T}A(x)^{-1}\beta-1\bigr).$$
--   Then for $P_0$-almost every $x$, for every $(\beta,\lambda)\in\mathbb U_1$:
--
--   1. (a) $\Gamma^*(\beta,\lambda;x)\neq\emptyset$;
--   2. $\lambda\mapsto\ell_{\rm rob}(\beta,\lambda;x)$ is finite near $\lambda$ and absolutely continuous on every interval with endpoints in $(\lambda_{thr}(\beta),\infty)$;
--   3. (12c), (12d): its left and right derivatives are
--   $$\frac{\partial_-\ell_{\rm rob}}{\partial\lambda}(\beta,\lambda;x)=\min_{\gamma\in\Gamma^*(\beta,\lambda;x)}-\sqrt\delta\bigl(\gamma^2\beta^{\mathsf T}A(x)^{-1}\beta-1\bigr),\qquad \frac{\partial_+\ell_{\rm rob}}{\partial\lambda}(\beta,\lambda;x)=\max_{\gamma\in\Gamma^*(\beta,\lambda;x)}-\sqrt\delta\bigl(\gamma^2\beta^{\mathsf T}A(x)^{-1}\beta-1\bigr),$$
--   both minimum and maximum being attained;
--   4. $\lambda\mapsto\ell_{\rm rob}(\beta,\lambda;x)$ is differentiable at $\lambda$ if and only if $\{\partial_\lambda F(\gamma,\beta,\lambda;x):\gamma\in\Gamma^*(\beta,\lambda;x)\}$ is a singleton.
--
--   This is the envelope-theorem description of the robust loss in the multiplier $\lambda$; integrated over $x$ it yields the one-sided derivatives of the dual objective used to locate the dual optimizer.
--
--   **Formalization Note** Only part (a) and the $\lambda$-part of part (b) are formalized; the $\beta_j$-derivatives (12a), (12b), the absolute continuity in $\beta_j$, the $\beta_j$-differentiability criterion and (13) are omitted. Because $F$ is affine in $\lambda$, both one-sided partial derivatives $\partial_\pm F/\partial\lambda$ equal $-\sqrt\delta(\gamma^2\beta^{\mathsf T}A(x)^{-1}\beta-1)$, so the page's set $\{\partial_+F/\partial\lambda,\partial_-F/\partial\lambda:\gamma\in\Gamma^*\}$ is the image written here. One-sided derivatives are `HasDerivWithinAt` on $(-\infty,\lambda]$ and $[\lambda,\infty)$ of the real-valued map $l\mapsto\ell_{\rm rob}(\beta,l;x)$, which is finite near $\lambda$ (stated as a conjunct). "Absolutely continuous for $(\beta,\lambda)\in\mathbb U_1$" is read as absolute continuity on every compact interval inside $(\lambda_{thr}(\beta),\infty)$. The "$P_0$-almost every $x$" quantifier is placed before $(\beta,\lambda)$, as on the page: one null set serves all $(\beta,\lambda)\in\mathbb U_1$. $\ell=\max_i\ell_i$ is written as: $\ell(u)$ is the greatest element of $\{\ell_i(u)\}$.
-- source:
--   arXiv:1810.02403v3, Proposition 2(a) and (b) (12c)–(12d), p. 16; proof pp. 48–49

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting

open MeasureTheory Filter Topology

namespace OTDRO.WorstCase

/-- **Proposition 2**, part (a) and the `λ`-part of (b) (arXiv:1810.02403v3, p. 16; proof
pp. 48–49): for `ℓ = max_{i ≤ K} ℓᵢ` with `ℓᵢ` continuously differentiable and `ℓ` satisfying
Assumption 2, for `P₀`-almost every `x` and every `(β, λ) ∈ 𝕌₁`: `Γ*(β, λ; x) ≠ ∅`;
`λ ↦ ℓ_rob(β, λ; x)` is finite near `λ` and absolutely continuous on every interval inside
`(λ_thr(β), ∞)`; its left and right derivatives are the minimum (12c) and the maximum (12d) of
`−√δ(γ² βᵀA(x)⁻¹β − 1)` over `γ ∈ Γ*(β, λ; x)`; and it is differentiable at `λ` if and only if
the set `{∂±F/∂λ(γ, β, λ; x) : γ ∈ Γ*(β, λ; x)} = {−√δ(γ²βᵀA(x)⁻¹β − 1) : γ ∈ Γ*}` is a
singleton. -/
theorem ellRob_lambda_derivatives {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P0] (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax) (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (K : ℕ) (hK : 0 < K) (ℓi : Fin K → ℝ → ℝ) (hℓi : ∀ i, ContDiff ℝ 1 (ℓi i))
    (hmax : ∀ u, IsGreatest (Set.range fun i => ℓi i u) (ℓ u)) :
    ∀ᵐ x ∂P0, ∀ β ∈ B, ∀ lam : ℝ, OTDRO.Dual.lamThr P0 ℓ A δ β < lam →
      (OTDRO.Dual.maximizers ℓ A δ β lam x).Nonempty ∧
      (∀ᶠ l in 𝓝 lam, OTDRO.Dual.ellRob ℓ A δ β l x ≠ ⊤) ∧
      (∀ a b : ℝ, OTDRO.Dual.lamThr P0 ℓ A δ β < a → OTDRO.Dual.lamThr P0 ℓ A δ β < b →
        AbsolutelyContinuousOnInterval (fun l => (OTDRO.Dual.ellRob ℓ A δ β l x).toReal) a b) ∧
      (∃ m : ℝ, IsLeast ((fun γ => -Real.sqrt δ * (γ ^ 2 * OTDRO.Dual.quadInv A β x - 1)) ''
          OTDRO.Dual.maximizers ℓ A δ β lam x) m ∧
        HasDerivWithinAt (fun l => (OTDRO.Dual.ellRob ℓ A δ β l x).toReal) m (Set.Iic lam) lam) ∧
      (∃ M : ℝ, IsGreatest ((fun γ => -Real.sqrt δ * (γ ^ 2 * OTDRO.Dual.quadInv A β x - 1)) ''
          OTDRO.Dual.maximizers ℓ A δ β lam x) M ∧
        HasDerivWithinAt (fun l => (OTDRO.Dual.ellRob ℓ A δ β l x).toReal) M (Set.Ici lam) lam) ∧
      (DifferentiableAt ℝ (fun l => (OTDRO.Dual.ellRob ℓ A δ β l x).toReal) lam ↔
        ∃ s : ℝ, (fun γ => -Real.sqrt δ * (γ ^ 2 * OTDRO.Dual.quadInv A β x - 1)) ''
          OTDRO.Dual.maximizers ℓ A δ β lam x = {s}) := by sorry

end OTDRO.WorstCase
