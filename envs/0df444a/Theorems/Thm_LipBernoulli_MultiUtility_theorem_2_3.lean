-- Prove2me | Theorems.Thm_LipBernoulli_MultiUtility_theorem_2_3
-- name    : LipBernoulli.MultiUtility.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:10.860012+00:00
-- url     : https://prove2.me/theorems/244038b3-b774-43be-9d07-7c6bdf7b7103
-- title:
--   Theorem 2.3, p. 7 — KR(X)* ≅ Lip0(X) for a separable pointed metric space X
-- statement:
--   Let $X$ be a separable metric space with its Borel $\sigma$-algebra and a base point $e \in X$, and let $\mathrm{Lip}_0(X)$ be the space of Lipschitz functions $u$ on $X$ with $u(e) = 0$, normed by the Lipschitz number. The map sending $u$ to the functional $\mu \mapsto \int_X u\,\mathrm d\mu$ on $\mathrm{KR}(X)$ is an isometric isomorphism $\mathrm{Lip}_0(X) \cong \mathrm{KR}(X)^*$. Concretely:
--
--   1. if $u(e) = 0$ and $u$ is $L$-Lipschitz, then $\mu \mapsto \int u\,\mathrm d\mu$ is additive and $\mathbb R$-homogeneous on $\mathrm{KR}(X)$ and $\big|\int u\,\mathrm d\mu\big| \le L\,\|\mu\|_{\mathrm{KR}}$;
--   2. if $\Phi$ is additive and $\mathbb R$-homogeneous on $\mathrm{KR}(X)$ with $|\Phi(\mu)| \le C\,\|\mu\|_{\mathrm{KR}}$ for all $\mu\in\mathrm{KR}(X)$, then there is a $C$-Lipschitz $u$ with $u(e)=0$ and $\Phi(\mu) = \int_X u\,\mathrm d\mu$ for all $\mu \in \mathrm{KR}(X)$;
--   3. two Lipschitz functions vanishing at $e$ that induce the same functional on $\mathrm{KR}(X)$ are equal.
--
--   In words: every bounded linear functional on $\mathrm{KR}(X)$ is integration against a Lipschitz function, which is how the separation argument of Theorem 4.6 produces Lipschitz Bernoulli utilities.
--
--   **Formalization Note** No normed-space instance is built on $\mathrm{KR}(X)$; the dual is described by linear functionals bounded with respect to $\|\cdot\|_{\mathrm{KR}}$. Parts 1 and 2 with the same constant say that the functional norm of $u$ equals its Lipschitz number (isometry), part 2 is surjectivity, part 3 injectivity. The base point is an explicit argument $e$, the page's "pointed". Constants are nonnegative reals and bounds are in $[0,\infty]$.
-- source:
--   Ok & Weaver, Lipschitz Bernoulli Utility Functions, arXiv:2104.11205v1, Theorem 2.3, p. 7

import Mathlib
import Definitions.Def_LipBernoulli_MultiUtility_Setting
import Definitions.Def_LipBernoulli_MultiUtility_KR

open MeasureTheory
open scoped ENNReal NNReal

namespace LipBernoulli.MultiUtility

/-- Theorem 2.3, p. 7: `KR(X)* ≅ Lip₀(X)` for a separable metric space `X` pointed at `e`, through
`u ↦ (μ ↦ ∫ u dμ)`. (a) every `u ∈ Lip₀(X)` with Lipschitz constant `L` gives a linear functional on
`KR(X)` of norm at most `L`; (b) every linear functional `Φ` on `KR(X)` with `|Φ μ| ≤ C ‖μ‖_KR` is
integration against some `C`-Lipschitz `u` vanishing at `e`; (c) `u` is determined by its functional.
(a) and (b) with the same `C` make the bijection isometric. -/
theorem theorem_2_3 {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (e : X) :
    (∀ (u : X → ℝ) (L : ℝ≥0), u e = 0 → LipschitzWith L u →
      (∀ μ ∈ KR X, ∀ ν ∈ KR X, krIntegral (μ + ν) u = krIntegral μ u + krIntegral ν u) ∧
      (∀ c : ℝ, ∀ μ ∈ KR X, krIntegral (c • μ) u = c * krIntegral μ u) ∧
      (∀ μ ∈ KR X, ENNReal.ofReal |krIntegral μ u| ≤ (L : ℝ≥0∞) * krNorm μ)) ∧
    (∀ (Φ : SignedMeasure X → ℝ) (C : ℝ≥0),
      (∀ μ ∈ KR X, ∀ ν ∈ KR X, Φ (μ + ν) = Φ μ + Φ ν) →
      (∀ c : ℝ, ∀ μ ∈ KR X, Φ (c • μ) = c * Φ μ) →
      (∀ μ ∈ KR X, ENNReal.ofReal |Φ μ| ≤ (C : ℝ≥0∞) * krNorm μ) →
      ∃ u : X → ℝ, u e = 0 ∧ LipschitzWith C u ∧ ∀ μ ∈ KR X, Φ μ = krIntegral μ u) ∧
    (∀ u v : X → ℝ, u e = 0 → v e = 0 →
      (∃ L : ℝ≥0, LipschitzWith L u) → (∃ L : ℝ≥0, LipschitzWith L v) →
      (∀ μ ∈ KR X, krIntegral μ u = krIntegral μ v) → u = v) := by sorry

end LipBernoulli.MultiUtility
