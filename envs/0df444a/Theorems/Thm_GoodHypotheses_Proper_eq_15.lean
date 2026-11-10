-- Prove2me | Theorems.Thm_GoodHypotheses_Proper_eq_15
-- name    : GoodHypotheses.Proper.eq_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:15:46.851757+00:00
-- url     : https://prove2.me/theorems/aa9d9718-3ac6-4da9-9262-cbd5f7fa6de5
-- title:
--   §4.2, Eq. (15) — distance penalty: E[ℓ̂_i] ≤ d_TV(h_i, p) − d_TV(h_i, ρ)
-- statement:
--   Let $h_i$ and $p$ be probability densities, $\rho$ a nonnegative integrable proxy, $\nu$ the density of a distribution with $\rho\le C\nu$ (Proxy Assumption 2), $S_i$ a Scheffé function of $(h_i,\rho)$, $X\sim\nu$ and $Y\sim p$ independent, and $r=\rho/\nu$. The empirical loss
--   $$\hat\ell_i=-S_i(Y)+r(X)S_i(X)+\frac{1-r(X)}2\qquad\text{(Eq. (18))}$$
--   satisfies the distance-penalty property
--   $$\ell_i=\mathbb E[\hat\ell_i]\le d_{TV}(h_i,p)-d_{TV}(h_i,\rho).$$
--
--   Differences from the source:
--
--   - encoding: S a Scheffé function (Definition 3) → IsScheffe and S measurable; reason: the integrals ∫ fS dµ of the statement presuppose that S is measurable
--   - encoding: densities ψ of distributions, draws X ∼ ψ → a ProbabilityMeasure P with P = ψ·μ (IsDensityOf: ψ measurable, nonnegative), X drawn from P; two draws from the product law; reason: Lean represents a draw by its law; independence does not change the expectation of a sum
--   - encoding: the expected empirical loss satisfies the distance-penalty inequality → the empirical loss is integrable for the product law and its integral satisfies the same inequality; reason: Lean's integral of a non-integrable function is 0; the paper's expectation exists
--   - encoding: the samples Z^t_i ∼ h_i of (17) → omitted; reason: ℓ̂^t_i does not depend on them; the paper notes they are never used (p. 19)
--   - encoding: ρ^t a proxy (nonnegative integrable density) → ρ : X → ℝ nonnegative everywhere and μ-integrable; reason: Definition 2's proxies
-- source:
--   Aamand, Aliakbarpour, Chen, Silwal, Stevens, Zou, A Good Way to Find Good Hypotheses, STOC 2027 submission (manuscript sha256 a428fbe0…), p. 19, §4.2, Eq. (15) (stated p. 17, derived pp. 18–19)

import Mathlib
import Definitions.Def_GoodHypotheses_Proper_Proxies

open MeasureTheory

namespace GoodHypotheses.Proper

/-- §4.2, Eq. (15) (pp. 17–19): let `h_i` and `p` be probability densities (`p` the density of
the law `Pp`), `ρ` a nonnegative integrable proxy, `ν` the density of a probability law `Pν`
with `ρ ≤ C ν` (Proxy Assumption 2), `S_i` a (measurable) Scheffé function of `(h_i, ρ)`,
`X ∼ Pν` and `Y ∼ Pp` independent, `r = ρ/ν`. The empirical loss
`ℓ̂_i = −S_i(Y) + r(X) S_i(X) + (1 − r(X))/2` (Eq. (18)) is integrable and its expectation
satisfies the distance-penalty property `ℓ_i = E[ℓ̂_i] ≤ dTV(h_i, p) − dTV(h_i, ρ)`. -/
theorem eq_15 {X : Type*} [MeasurableSpace X] (μ : Measure X) (hi p ρ ν S : X → ℝ)
    (Pp Pν : ProbabilityMeasure X) (C : ℝ)
    (hhi : IsProbDensity μ hi) (hp : IsDensityOf μ Pp p) (hν : IsDensityOf μ Pν ν)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ : Integrable ρ μ) (hρν : ∀ x, ρ x ≤ C * ν x)
    (hS : IsScheffe hi ρ S) (hSm : Measurable S) :
    Integrable (fun z : X × X => empiricalLoss S ρ ν z.1 z.2)
        ((Pν : Measure X).prod (Pp : Measure X)) ∧
      ∫ z, empiricalLoss S ρ ν z.1 z.2 ∂((Pν : Measure X).prod (Pp : Measure X))
        ≤ tvDist μ hi p - tvDist μ hi ρ := by sorry

end GoodHypotheses.Proper
