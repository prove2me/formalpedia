-- Prove2me | Theorems.Thm_KingRockAsymp_Distribution_theorem_2_4
-- name    : KingRockAsymp.Distribution.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:58:14.845067+00:00
-- url     : https://prove2.me/theorems/2fc0a726-983a-48f9-8a15-2bc5e21f78be
-- title:
--   Theorem 2.4 — bounds in probability on solutions of a generalized equation with random data
-- statement:
--   Let $Z$ be a separable Banach space, $f : Z \times \mathbb R^n \to \mathbb R^m$, $N : \mathbb R^n \rightrightarrows \mathbb R^m$, $z^* \in Z$ and $x^* \in \mathbb R^n$. Suppose that, for some $\alpha$, $f$ satisfies the Lipschitz condition
--   $$|f(z^*,x) - f(z,x)| \le \alpha \|z^* - z\| \qquad \text{for all } z \in Z$$
--   uniformly for all $x$ in a neighborhood of $x^*$. Let $F = f(z^*,\cdot) + N$, assume $0 \in F(x^*)$, and suppose that
--   $$DF^{-1}(0|x^*)(0) = \{0\}.$$
--   Then there exist a neighborhood $U$ of $x^*$, a constant $\lambda \ge 0$ and a threshold $\delta_0 > 0$ with the following property. For every probability space $(\Omega, P)$ and all measurable random elements $x^\nu : \Omega \to \mathbb R^n$, $z^\nu : \Omega \to Z$ such that, for every $\omega$, $x^\nu(\omega)$ solves the generalized equation $0 \in f(z^\nu(\omega), x) + N(x)$ and lies in $U$,
--   $$P\{|x^\nu - x^*| > \delta\} \le P\{\alpha\lambda\|z^\nu - z^*\| > \delta\} \qquad \text{for all } 0 < \delta < \delta_0.$$
--
--   The theorem converts a bound on the data error $\|z^\nu - z^*\|$ into a bound in probability on the solution error, under the sole condition that the contingent derivative of $F^{-1}$ is single-valued at $0$.
--
--   **Formalization Note** The hypothesis $0 \in F(x^*)$ is presupposed by the paper's notation $DF^{-1}(0|x^*)$ and is stated explicitly. "For all sufficiently small $\delta > 0$" is read with the threshold $\delta_0$ chosen together with $U$ and $\lambda$, before the random elements, which is what the paper's order ("there exist $U$ and $\lambda$ such that if $x^\nu$ … one has … for all sufficiently small $\delta$") says. The random elements are measurable and live in an arbitrary universe-polymorphic probability space; $Z$ carries its Borel sigma-algebra.
-- source:
--   King & Rockafellar, Asymptotic Theory for Solutions in Statistical Estimation and Stochastic Programming, Math. Oper. Res. 18(1) (1993), Theorem 2.4, p. 6 (authors' manuscript pagination)

import Mathlib
import Definitions.Def_KingRockAsymp_Distribution_Basic

namespace KingRockAsymp.Distribution

open Set Filter Topology Metric MeasureTheory ProbabilityTheory

universe u in
theorem theorem_2_4 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [TopologicalSpace.SeparableSpace Z] [MeasurableSpace Z] [BorelSpace Z] {n m : ℕ}
    (f : Z → Rn n → Rn m) (N : Rn n → Set (Rn m)) (z₀ : Z) (x₀ : Rn n) (α : ℝ)
    (hlip : ∃ V ∈ 𝓝 x₀, ∀ x ∈ V, ∀ z : Z, ‖f z₀ x - f z x‖ ≤ α * ‖z₀ - z‖)
    (h0 : (0 : Rn m) ∈ fPlusN f N z₀ x₀)
    (hD : contingentDeriv (svInv (fPlusN f N z₀)) 0 x₀ 0 = {0}) :
    ∃ U ∈ 𝓝 x₀, ∃ lam : ℝ, 0 ≤ lam ∧ ∃ δ₀ > (0 : ℝ),
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (xν : Ω → Rn n) (zν : Ω → Z), Measurable xν → Measurable zν →
        (∀ ω, xν ω ∈ solMap f N (zν ω) ∩ U) →
        ∀ δ : ℝ, 0 < δ → δ < δ₀ →
          P {ω | δ < ‖xν ω - x₀‖} ≤ P {ω | δ < α * lam * ‖zν ω - z₀‖} := by sorry

end KingRockAsymp.Distribution
