-- Prove2me | Theorems.Thm_ObsArrivalPricing_lemma_3
-- name    : ObsArrivalPricing.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:43:28.438138+00:00
-- url     : https://prove2.me/theorems/f9dd234f-d3c6-43ac-b504-ed38bb5758f1
-- title:
--   Lemma 3 — $R^{uo}_\tau\ge\frac{(1-c)^2}{2\ln(1/c)}R_\tau$
-- statement:
--   Fix an instance ($F$ on $[0,\bar v]$, $0<\delta<\mu$), $c\in(0,1)$ and $T=\ln(1/c)/\delta$, and write $\kappa=\frac{1-c}{2\ln(1/c)}$. For every admissible price function $p$ and every arrival time $\tau\ge0$,
--   $$\kappa\,e^{-\delta\tau}\,\mathrm{Rev}_0(p)\;\le\;R^{uo}_\tau(p)+\kappa\,c\,e^{-\delta\tau}R_0,$$
--   where $R^{uo}_\tau(p)$ is the seller's expected revenue in the unobservable case when the buyer arrives at $\tau$, under the randomly shifted periodic policy $\hat p_{t_0}$ built from $p$ with $t_0\sim\mathrm{Unif}[0,2T]$, $\mathrm{Rev}_0(p)$ is the revenue of $p$ from a buyer arriving at $0$, and $R_0$ is the optimal value of $[SPO_0]$.
--
--   For an optimal $p$ ($\mathrm{Rev}_0(p)=R_0$) this is the printed bound
--   $$R^{uo}_\tau\ \ge\ \frac{(1-c)^2}{2\ln(1/c)}\,R_\tau,\qquad R_\tau=e^{-\delta\tau}R_0 .$$
--   It holds for every arrival time, which is why the bound on the value of observability does not depend on the arrival distribution.
--
--   Differences from the source:
--   - generalization: $p$ is the optimal price function of $[SPO_0]$ ($\hat p$ built from "the policy $p$ that solves the observable case formulation", p.18) → every admissible price function $p$, in additive form; reason: at an optimal $p$ (with $\mathrm{Rev}_0(p)=R_0<\infty$) the Lean statement is the printed one; the paper never proves that an optimal $p$ exists
--   - encoding: $T=\ln(1/c)/\delta$ → hypothesis $0<\delta$; reason: the printed $T$ is defined only for $\delta>0$
--   - encoding: $R^{uo}_\tau$, the expected revenue of the randomly shifted $\hat p$ given arrival $\tau$ → $\frac1{2T}\int_0^{2T}\int r(\hat p_{t_0},\tau,v)\,dF(v)\,dt_0$ as lower Lebesgue integrals; reason: the randomization $t_0\sim\mathrm{Unif}[0,2T]$ of Proposition 3
--   - generalization: valuation cdf $F$ with density $f$ on $[0,\bar v]$ (p.8) → any Borel probability law $F$ with $F([0,\bar v]^c)=0$ (atoms allowed); reason: the paper's instances are special cases; the statement does not use the density
-- source:
--   Correa, Pizarro & Vulcano, The Value of Observing the Buyer Arrival Time in Dynamic Pricing, SSRN 3541494 (rev. Oct 2022), Lemma 3, p.23; proof pp.A7–A9; R_τ = e^{−δτ}R0, p.11

import Mathlib
import Definitions.Def_ObsArrivalPricing_PeriodicPolicy

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ObsArrivalPricing

/-- Lemma 3 (SSRN 3541494, p.23; proof pp.A7–A9), for every admissible price function. For
`c ∈ (0,1)`, `T = ln(1/c)/δ`, an admissible `p` and an arrival time `τ ≥ 0`, the expected revenue
`R^uo_τ` of the randomly shifted `p̂` satisfies
`κ e^{−δτ} Rev0(p) ≤ R^uo_τ + κ c e^{−δτ} R0` with `κ = (1 − c)/(2 ln(1/c))`. For an optimal `p`
(`Rev0(p) = R0`) this is the printed `R^uo_τ ≥ ((1 − c)²/(2 ln(1/c))) R_τ`, `R_τ = e^{−δτ} R0`. -/
theorem lemma_3 (I : ProblemInstance) (hδ : 0 < I.δ) {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1)
    {p : ℝ → ℝ} (hp : IsAdmissible I.vbar p) {τ : ℝ} (hτ : 0 ≤ τ) :
    ENNReal.ofReal ((1 - c) / (2 * Real.log (1 / c)) * Real.exp (-I.δ * τ)) *
        Rev0 I.F I.δ I.μ p ≤
      RuoTau I.F I.δ I.μ p (Real.log (1 / c) / I.δ) τ +
        ENNReal.ofReal ((1 - c) / (2 * Real.log (1 / c)) * c * Real.exp (-I.δ * τ)) *
          R0 I.vbar I.F I.δ I.μ := by sorry

end ObsArrivalPricing
