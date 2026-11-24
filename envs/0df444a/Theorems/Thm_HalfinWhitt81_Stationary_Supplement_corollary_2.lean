-- Prove2me | Theorems.Thm_HalfinWhitt81_Stationary_Supplement_corollary_2
-- name    : HalfinWhitt81.Stationary.Supplement.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:50:53.786302+00:00
-- url     : https://prove2.me/theorems/bbb8856b-d8c4-41a1-b5a7-40387c7c1918
-- title:
--   Corollary 2 — the long-time law Y(∞) of the Theorem 2 diffusion is the hybrid law X of Theorem 1
-- statement:
--   Fix $\mu>0$ and $\beta>0$, and let $\alpha=\varphi(\beta)/(\varphi(\beta)+\beta\Phi(\beta))$, where $\varphi$ and $\Phi$ are the standard normal density and distribution function. Let $X$ be the law of Theorem 1:
--
--   $$P(X\ge0)=\alpha,\qquad P(X>x\mid X\ge0)=e^{-x\beta}\ (x\ge0),\qquad P(X\le x\mid X\le0)=\frac{\Phi(\beta+x)}{\Phi(\beta)}\ (x\le0).$$
--
--   Let $Y$ be the diffusion of Theorem 2, with drift $-\mu\beta$ for $x\ge0$, $-\mu(x+\beta)$ for $x\le0$ and infinitesimal variance $2\mu$, started from an arbitrary initial law. Then the limiting distribution $Y(\infty)$, defined by $P(Y(\infty)\le x)=\lim_{t\to\infty}P(Y(t)\le x)$, exists and has the same distribution as $X$:
--
--   $$Y(t)\Rightarrow X\qquad(t\to\infty),$$
--
--   whatever the law of $Y(0)$.
--
--   The corollary says that the two limits — first $n\to\infty$, then $t\to\infty$, and the reverse order — agree, so the stationary law of the limiting diffusion is the limit of the stationary queue laws.
--
--   **Formalization Note** The statement produces one law $X$ satisfying the three properties (which determine it) and then asserts, for every initial law $\nu$ and every solution of the Theorem 2 equation $dY=m(Y)\,dt+\sqrt{2\mu}\,dB$ with $Y(0)\sim\nu$ independent of $B$, that $E\,g(Y(t))\to\int g\,dX$ as $t\to\infty$ for every bounded continuous $g$. The order of quantifiers makes the limit independent of the initial law.
--
--   Differences from the source:
--
--   - encoding: P(Y(∞) ≤ x) = lim_{t→∞} P(Y(t) ≤ x) for all x → E g(Y(t)) → ∫ g dX for every bounded continuous g; reason: equivalent because X has a continuous distribution function
--   - reading: "Y(∞) has the same distribution as X", with Y the diffusion of Theorem 2 → for every initial law, every solution of the Theorem 2 equation has Y(t) ⇒ X; reason: the proof (p. 578) ends "since the distribution of Y(∞) is independent of the initial distribution"; Y(∞) is defined on p. 578 as the t → ∞ limit
-- source:
--   Halfin and Whitt, Heavy-Traffic Limits for Queues with Many Exponential Servers, Operations Research 29 (1981), p. 578, Corollary 2 (Y(∞) defined in the display before it)

import Mathlib
import Definitions.Def_ErlangA_Diffusion_SDE
import Definitions.Def_QueueingFundamentals_BirthDeath_Erlang

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace HalfinWhitt81.Stationary.Supplement

open ErlangA.Diffusion QueueingFundamentals.BirthDeath

/-- Halfin–Whitt (1981), Corollary 2, p. 578. Let `μ > 0`, `β > 0`. There is a probability law
`X` on `ℝ` (the law of Theorem 1: `P(X ≥ 0) = α(β)`, `P(X > x | X ≥ 0) = e^{−xβ}` for `x ≥ 0`,
`P(X ≤ x | X ≤ 0) = Φ(β + x)/Φ(β)` for `x ≤ 0`) such that every solution `Y` of the diffusion of
Theorem 2 (drift `−μβ` on `x ≥ 0`, `−μ(x + β)` on `x ≤ 0`, variance `2μ`), whatever its initial
law, has `Y(t) ⇒ X` as `t → ∞`. -/
theorem corollary_2 (μ β : ℝ) (hμ : 0 < μ) (hβ : 0 < β) :
    ∃ X : ProbabilityMeasure ℝ,
      (X : Measure ℝ).real (Set.Ici 0) = halfinWhittAlpha β ∧
      (∀ x : ℝ, 0 ≤ x →
        (X : Measure ℝ).real (Set.Ioi x) / (X : Measure ℝ).real (Set.Ici 0) =
          Real.exp (-(x * β))) ∧
      (∀ x : ℝ, x ≤ 0 →
        (X : Measure ℝ).real (Set.Iic x) / (X : Measure ℝ).real (Set.Iic 0) =
          cdf (gaussianReal 0 1) (β + x) / cdf (gaussianReal 0 1) β) ∧
      ∀ (ν : Measure ℝ) (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω')
        (b : ℝ≥0 → Ω' → ℝ) (q : Ω' → ℝ → ℝ),
        IsDiffusionSolution P' μ β 0 ν b q →
        ∀ g : ℝ →ᵇ ℝ, Tendsto (fun t : ℝ => ∫ ω, g (q ω t) ∂P') atTop
          (𝓝 (∫ x, g x ∂(X : Measure ℝ))) := by sorry

end HalfinWhitt81.Stationary.Supplement
