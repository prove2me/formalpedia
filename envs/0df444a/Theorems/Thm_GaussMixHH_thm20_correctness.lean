-- Prove2me | Theorems.Thm_GaussMixHH_thm20_correctness
-- name    : GaussMixHH.thm20_correctness
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:34:24.946141+00:00
-- url     : https://prove2.me/theorems/c83e80fe-03a7-450f-a4dd-c1cef5954491
-- title:
--   Proof of Theorem 20, p.28 — correctness: every $\Gamma^2/100$-approximate minimizer of $f$ has near-mass error $<\eta$
-- statement:
--   Let $\Gamma>0$, $\xi=\Gamma/1000$, $U$ a grid, $\theta_1,\dots,\theta_H$ frequencies ($H\ge1$), $\hat\Phi_1,\dots,\hat\Phi_H\in\mathbb C$ the empirical test values, $\rho$ a radial distribution and $x^*$ a grid probability vector with $\operatorname{near-mass}_R(x^*)=\operatorname{near-mass}_R(\rho)$. Assume
--
--   1. the grid bound $|\Phi_\rho(\theta_t)-\Phi_{x^*}(\theta_t)|\le\xi$ and the sampling bound (9) $|\hat\Phi_t-\Phi_\rho(\theta_t)|\le\xi$ for every $t$;
--   2. (8) for all pairs of grid probability vectors;
--   3. the defining property of $\Gamma$: every grid probability vector $x$ with $|\operatorname{near-mass}_R(x)-\operatorname{near-mass}_R(x^*)|\ge\eta$ has $\mathbb E_{\theta\sim\mathrm{Unif}(I)}|\Phi_x(\theta)-\Phi_{x^*}(\theta)|^2\ge16\Gamma^2$.
--
--   Then every grid probability vector $x$ with $f(x)\le\min f+\Gamma^2/100$, where $f(x)=\frac1H\sum_t|\Phi_x(\theta_t)-\hat\Phi_t|^2$ and the minimum is over grid probability vectors, satisfies
--
--   $$|\operatorname{near-mass}_R(x)-\operatorname{near-mass}_R(\rho)|<\eta .$$
--
--   This is the deterministic core of Theorem 20: on the good events the output of the fitted convex program has the right near mass.
--
--   Differences from the source:
--   - encoding: "Condition on the events in (8) and (9)" and the grid approximation bound → these bounds as hypotheses at the sampled frequencies; reason: the paragraph's argument is conditional on them
--   - encoding: "Choose Γ = c√λe^{−CA} so that the separation guaranteed by Proposition 19 is at least 16Γ²" (p.26) → that separation for grid vectors as a hypothesis on Γ; reason: it is the defining property of Γ; Proposition 19 (a milestone) supplies it
--   - encoding: "our approximate minimizer" with objective at most Γ²/100 above the minimum → f(x) ≤ sInf f(simplex) + Γ²/100; reason: the minimum over the nonempty simplex is the infimum of a set bounded below by 0
--   - generalization: U, θ_t, x∗ = Pρz of the proof → any grid, frequencies, values Φ̂_t and probability vector x* with the stated bounds; reason: the chain uses only these bounds
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), proof of Theorem 20, "Correctness", p.28 (PDF p.30); Γ and the tolerance Γ²/100 on p.26

import Mathlib
import Definitions.Def_GaussMixHH_GridFit
import Definitions.Def_GaussMixHH_Gapped

open MeasureTheory Complex

namespace GaussMixHH

/-- **Proof of Theorem 20, correctness** (every approximate minimizer of `f` has near-mass error
less than `η`).

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), proof of Theorem 20, "Correctness",
p.28 (PDF p.30); `f`, `Γ` and the tolerance `Γ²/100` are on p.26.

"The grid approximation x∗ = Pρz of the true radial probability distribution ρz has the true near
mass. By the grid approximation bound and (9), for every sampled frequency we have
|Φ_{x∗}(θt) − Φ̂z(θt)| ≤ ξ + ξ = 2ξ. Since f(x∗) is the average of these squared errors,
f(x∗) ≤ 4ξ². If a grid vector x has near-mass error at least η, its average squared difference from
x∗ over I is at least 16Γ². Applying (8) to x and x∗ gives … > 15Γ². … f(x) ≥ (√15Γ − 2ξ)² > 9Γ².
In contrast, our approximate minimizer satisfies f(x) ≤ 4ξ² + Γ²/100 < Γ²/50. Its near-mass error
must therefore be less than η."

**Formalization Note.** The deterministic implication, with `ξ = Γ/1000`, conditioned on the
events of the proof as hypotheses: the grid bound `|Φ_ρ(θ_t) − Φ_{x*}(θ_t)| ≤ ξ` and (9)
`|Φ̂_t − Φ_ρ(θ_t)| ≤ ξ` at every sampled frequency, where `x*` is a probability vector on the grid
with the true near mass `near-mass_R(ρ)`; (8) for all pairs of probability vectors; and the defining
property of `Γ` (p.26, "Choose Γ = c√λe^{−CA} so that the separation guaranteed by Proposition 19
is at least 16Γ²"): every probability vector `x` with near-mass error at least `η` from `x*` has
`E_{θ∼Unif(I)}|Φ_x − Φ_{x*}|² ≥ 16Γ²`. Conclusion: every probability vector `x` with
`f(x) ≤ min f + Γ²/100` has `|near-mass(x) − near-mass_R(ρ)| < η`. The minimum of `f` over the
simplex is the real `sInf` of its values, a nonempty set bounded below by `0`. -/
theorem thm20_correctness (n : ℕ) (R η Γ θ₀ q : ℝ) (ρ : MeasureTheory.Measure ℝ) (G : Finset ℝ)
    (H : ℕ) (θs : Fin H → ℝ) (Φhat : Fin H → ℂ) (xstar : ℝ → ℝ) (hΓ : 0 < Γ) (hH : 0 < H)
    (hx : IsProbVec G xstar) (hnm : nearMassVec R G xstar = nearMass R ρ)
    (hgrid : ∀ t, ‖PhiRad n ρ (θs t) - PhiVec n G xstar (θs t)‖ ≤ Γ / 1000)
    (h9 : ∀ t, ‖Φhat t - PhiRad n ρ (θs t)‖ ≤ Γ / 1000)
    (h8 : ∀ x y : ℝ → ℝ, IsProbVec G x → IsProbVec G y →
      |empSqDiff n G θs x y - avgSqDiff n G θ₀ q x y| ≤ Γ ^ 2 / 25)
    (hsep : ∀ x : ℝ → ℝ, IsProbVec G x →
      η ≤ |nearMassVec R G x - nearMassVec R G xstar| → 16 * Γ ^ 2 ≤ avgSqDiff n G θ₀ q x xstar) :
    ∀ x : ℝ → ℝ, IsProbVec G x →
      fitObjective n G θs Φhat x ≤
        sInf (fitObjective n G θs Φhat '' {y | IsProbVec G y}) + Γ ^ 2 / 100 →
      |nearMassVec R G x - nearMass R ρ| < η := by sorry

end GaussMixHH
