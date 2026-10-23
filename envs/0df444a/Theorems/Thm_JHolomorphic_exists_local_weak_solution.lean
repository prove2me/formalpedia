-- Prove2me | Theorems.Thm_JHolomorphic_exists_local_weak_solution
-- name    : JHolomorphic.exists_local_weak_solution
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-20T20:32:41.827922+00:00
-- url     : https://prove2.me/theorems/44571feb-24a8-4be9-ae83-820b0a229bcc
-- title:
--   Local $W^{1,p}$ solutions of real-linear Cauchy–Riemann equations with prescribed value
-- statement:
--   Let $2<p<\infty$, let $D\subset\mathbb{C}$ be the open unit disc and let $A\in L^p(D,\operatorname{End}_{\mathbb{R}}(\mathbb{C}^n))$. For every $u_0\in\mathbb{C}^n$ and every sufficiently small $\varepsilon>0$ there is a continuous $u\in W^{1,p}(D_\varepsilon,\mathbb{C}^n)$ with $u(0)=u_0$ and
--   $$\partial_su+i\,\partial_tu+Au=0\quad\text{almost everywhere on }D_\varepsilon,$$
--   where $D_\varepsilon$ is the open disc of radius $\varepsilon$ and $\partial_su$, $\partial_tu$ are weak partial derivatives.
--
--   **Formalization Note** $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)` and $A$ has type `ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n)` with `MemLp A (ENNReal.ofReal p) (volume.restrict (ball 0 1))`. "Every sufficiently small $\varepsilon$" is `∀ᶠ ε in 𝓝[>] 0`. The weak partials are given by `HasWeakPartialsOn (ball 0 ε) u us ut`, and $u,u_s,u_t\in L^p(D_\varepsilon)$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 2, Lemma 2.24, p. 39

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric Filter Topology DbarRegularity
open scoped ContDiff ENNReal NNReal

/-- Wendl, Lemma 2.24 (p. 39): let `2 < p < ∞` and `A ∈ L^p(D, End_ℝ(ℂⁿ))` on the open unit disc
`D`. For every `u₀ ∈ ℂⁿ` and every sufficiently small `ε > 0` there is a continuous
`u ∈ W^{1,p}(D_ε)` with `u(0) = u₀` that solves `∂̄u + A u = 0` weakly on `D_ε`. -/
theorem exists_local_weak_solution (n : ℕ) (p : ℝ) (hp : 2 < p)
    (A : ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n))
    (hA : MemLp A (ENNReal.ofReal p) (volume.restrict (ball 0 1)))
    (u₀ : EuclideanSpace ℂ (Fin n)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ u : ℂ → EuclideanSpace ℂ (Fin n), ContinuousOn u (ball 0 ε) ∧
      u 0 = u₀ ∧ ∃ us ut : ℂ → EuclideanSpace ℂ (Fin n), HasWeakPartialsOn (ball 0 ε) u us ut ∧
        MemLp u (ENNReal.ofReal p) (volume.restrict (ball 0 ε)) ∧
        MemLp us (ENNReal.ofReal p) (volume.restrict (ball 0 ε)) ∧
        MemLp ut (ENNReal.ofReal p) (volume.restrict (ball 0 ε)) ∧
        ∀ᵐ z ∂(volume.restrict (ball 0 ε)), us z + Complex.I • ut z + A z (u z) = 0 := by
  sorry

end JHolomorphic
