-- Prove2me | Theorems.Thm_JHolomorphic_exists_memLp_weakDeriv_of_enorm_integral_le
-- name    : JHolomorphic.exists_memLp_weakDeriv_of_enorm_integral_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T20:56:21.842563+00:00
-- url     : https://prove2.me/theorems/7d17b6d7-b8b5-4952-b938-9f4ca2d6bf38
-- title:
--   An $L^q$-bounded distributional derivative is an $L^p$ weak derivative
-- statement:
--   Let $1<p<\infty$ and $q=p/(p-1)$, let $E$ be a finite-dimensional real normed space, let $U\subseteq\mathbb{C}$ be open, let $v\in\mathbb{C}$, and let $f:\mathbb{C}\to E$ be integrable on every compact subset of $U$. Suppose there is $C$ such that
--   $$\Bigl\|\int_{\mathbb{C}}\bigl(D\varphi(z)\,v\bigr)\,f(z)\,dz\Bigr\|\le C\,\|\varphi\|_{L^q(U)}$$
--   for every real $C^\infty$ function $\varphi$ with compact support in $U$. Then $f$ has a weak derivative in the direction $v$ on $U$ that lies in $L^p(U)$: there is $g\in L^p(U;E)$ with
--   $$\int_{\mathbb{C}}\bigl(D\varphi(z)\,v\bigr)\,f(z)\,dz=-\int_{\mathbb{C}}\varphi(z)\,g(z)\,dz$$
--   for every such $\varphi$. This characterizes $L^p$ weak directional derivatives by an $L^q$ bound on the distributional derivative.
--
--   **Formalization Note** Test functions satisfy `ContDiff ℝ ∞ φ`, `HasCompactSupport φ` and `tsupport φ ⊆ U`; integrals are over all of $\mathbb{C}$. The hypothesis uses the extended norm `‖·‖ₑ`, the bound `ENNReal.ofReal C`, and `eLpNorm φ (ENNReal.ofReal (p / (p - 1)))` for the Lebesgue measure restricted to `U`; membership $g\in L^p(U)$ is `MemLp g (ENNReal.ofReal p) (volume.restrict U)`.
-- source:
--   Standard; cf. L. C. Evans, Partial Differential Equations, §5.8.2, proof of Theorem 3 (ii); D. Gilbarg, N. Trudinger, Elliptic PDE of Second Order, Lemma 7.24

import Definitions.Def_JHolomorphic_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

namespace JHolomorphic

open MeasureTheory Metric
open scoped ContDiff ENNReal

/-- Let `1 < p < ∞`, `q = p / (p - 1)`, `U ⊆ ℂ` open, `f : ℂ → E` integrable on compact subsets of
`U`, and `v ∈ ℂ`. If `‖∫ (Dφ · v) f‖ ≤ C ‖φ‖_{L^q(U)}` for every real `C^∞` function `φ` with compact
support in `U`, then `f` has a weak derivative `g` in the direction `v` on `U`, i.e.
`∫ (Dφ · v) f = -∫ φ g` for all such `φ`, and `g ∈ L^p(U)`. -/
theorem exists_memLp_weakDeriv_of_enorm_integral_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 1 < p) {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → E} (hf : ∀ K ⊆ U, IsCompact K → IntegrableOn f K) (v : ℂ) (C : ℝ)
    (hC : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ‖∫ z, fderiv ℝ φ z v • f z‖ₑ ≤
        ENNReal.ofReal C * eLpNorm φ (ENNReal.ofReal (p / (p - 1))) (volume.restrict U)) :
    ∃ g : ℂ → E, MemLp g (ENNReal.ofReal p) (volume.restrict U) ∧
      ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ z, fderiv ℝ φ z v • f z = -∫ z, φ z • g z := by
  sorry

end JHolomorphic
