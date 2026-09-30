-- Prove2me | Theorems.Thm_InfoSharing_Economy_ex_ante_profits_manufacturers
-- name    : InfoSharing.Economy.ex_ante_profits_manufacturers
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T23:46:11.071522+00:00
-- url     : https://prove2.me/theorems/d25a7e08-61ed-4469-993b-0dd457583cdc
-- title:
--   §4.2 — the manufacturers' ex ante profits $\pi_M(0)$, $\pi_M^U(1)$, $\pi_M^I(1)$, $\pi_M(2)$ (production economy)
-- statement:
--   Let $\phi > 0$ and $0 < c_e < 2/(1+\phi)$, put $c = -c_e$, and let $a, b$ be reals. Let $(\theta, Y)$ satisfy the signal model with variance $\sigma^2$ and weight $\beta = \beta(t,\sigma)$, and let $E$ be any family of pricing equilibria with payoff table $M$. For every profile $X$ and manufacturer $i$,
--
--   $$M(X, i) = \begin{cases} \pi_M(0) & n(X) = 0, \\ \pi_M^U(1) & n(X) = 1,\ X_i = U, \\ \pi_M^I(1) & n(X) = 1,\ X_i = I, \\ \pi_M(2) & n(X) = 2, \end{cases}$$
--
--   where, with $\bar\pi_M = \frac{(1+\phi)(2+(1+\phi)c)(a-b)^2}{4(2+\phi+(1+\phi)c)^2}$,
--
--   $$\pi_M(0) = \bar\pi_M - \frac{c\beta\sigma^2}{4} - c(1-\beta)\sigma^2, \qquad \pi_M^U(1) = \bar\pi_M - \frac{c}{4}\left[\frac{2+3\phi+(1+\phi)(1+2\phi)c}{(1+\phi)(2+(1+\phi)c)}\right]^2\beta\sigma^2 - c(1-\beta)\sigma^2,$$
--
--   $$\pi_M^I(1) = \bar\pi_M + \frac{\beta\sigma^2}{4(1+\phi)(2+(1+\phi)c)} - c(1-\beta)\sigma^2, \qquad \pi_M(2) = \bar\pi_M + \frac{(1+\phi)(2+(1+\phi)c)}{4(2+\phi+(1+\phi)c)^2}\beta\sigma^2 - c(1-\beta)\sigma^2 .$$
--
--   These closed forms are the input of every comparison in Lemma 5 and Propositions 6–8.
--
--   **Formalization Note** The production economy model takes $c = -c_e$ with $0 < c_e < 2/(1+\phi)$ (the Assumption of p. 251). The ex ante profits are those of an equilibrium of the pricing game on the signal model, not the closed forms: the closed forms are the content of the §4.2 milestones. The production cost is the uncapped quadratic $bq - c_e q^2$ (the paper's cap at $\bar q = b/(2c_e)$ is assumed never to bind, footnote 11, p. 251). **Correction of the paper.** The single value $c_e^* = \frac{2+3\phi}{(1+2\phi)(1+\phi)}$ (which lies in $(1/(1+\phi), 2/(1+\phi))$) is excluded: there the slope $\phi(1+(1+\phi)c)/[(1+\phi)(2+(1+\phi)c)]$ of the best response (2) equals $-1$, so the pricing stage has a continuum of equilibria with different ex ante profits, and Lemma 1's uniqueness claim, on which the payoff table rests, fails.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 252, §4.2

import Mathlib
import Definitions.Def_InfoSharing_Shared_IsSignalModel
import Definitions.Def_InfoSharing_Shared_PayoffTable
import Definitions.Def_InfoSharing_Shared_ClosedForms
open MeasureTheory
open InfoSharing.Shared

namespace InfoSharing.Economy

/-- **§4.2, manufacturers' ex ante profits** (Shang, Ha & Tong 2016, p. 252), production
economy (`c = −c_e`) under the Assumption `c_e < 2/(1+φ)`. In the payoff table of every family
of pricing equilibria, manufacturer `i`'s ex ante profit is `π_M(0)`, `π_M(2)`, `π_M^I(1)` or
`π_M^U(1)` according to the number of informed manufacturers and his own status.

**Correction.** The value `c_e = (2+3φ)/((1+2φ)(1+φ))` is excluded: there the best-response
slope in (2) is `−1`, the pricing stage has a continuum of equilibria with different ex ante
profits, and Lemma 1's uniqueness (on which the paper's payoff table rests) fails. -/
theorem ex_ante_profits_manufacturers (φ ce c a b σ β : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (θ Y : Ω → ℝ) (E : (Fin 2 → Status) → PricingProfile)
    (hφ : 0 < φ) (hc : c = -ce) (hce : 0 < ce) (hA : ce < 2 / (1 + φ))
    (hU : ce ≠ (2 + 3 * φ) / ((1 + 2 * φ) * (1 + φ)))
    (hM : IsSignalModel μ θ Y σ β) (hE : IsPricingEqFamily μ θ Y a b c φ β E)
    (X : Fin 2 → Status) (i : Fin 2) :
    (numInformed X = 0 → (payoffTable μ θ Y a b c φ E).M X i = piM0 a b c φ σ β) ∧
    (numInformed X = 1 → X i = Status.uninformed →
      (payoffTable μ θ Y a b c φ E).M X i = piMU1 a b c φ σ β) ∧
    (numInformed X = 1 → X i = Status.informed →
      (payoffTable μ θ Y a b c φ E).M X i = piMI1 a b c φ σ β) ∧
    (numInformed X = 2 → (payoffTable μ θ Y a b c φ E).M X i = piM2 a b c φ σ β) := by sorry

end InfoSharing.Economy
