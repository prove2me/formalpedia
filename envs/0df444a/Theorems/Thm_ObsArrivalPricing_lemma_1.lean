-- Prove2me | Theorems.Thm_ObsArrivalPricing_lemma_1
-- name    : ObsArrivalPricing.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:42:56.608699+00:00
-- url     : https://prove2.me/theorems/2fc0288f-b8e3-476b-8c00-a412c934dd2b
-- title:
--   Lemma 1 — revenue up to $T=\ln(1/c)/\delta$ is at least $(1-c)R_0$
-- statement:
--   Fix an instance: a valuation law $F$ on $[0,\bar v]$ and discount rates $0<\delta<\mu$. Let $c\in(0,1)$ and $T=\ln(1/c)/\delta$. For every admissible price function $p$,
--   $$\mathrm{Rev}_0(p)\;\le\;R_{[0,T]}(p)+c\,R_0,$$
--   where $\mathrm{Rev}_0(p)$ is the seller's expected revenue from a buyer arriving at time $0$, $R_{[0,T]}(p)=p(0)(1-F(\psi(0)))+\int_0^Te^{-\delta t}p(t)\,d(1-F(\psi(t)))$ is the part of it collected from purchases at times $t\le T$, and $R_0$ is the optimal value of $[SPO_0]$.
--
--   For an optimal $p$ ($\mathrm{Rev}_0(p)=R_0$) this reads $R_{[0,T]}\ge(1-c)R_0$: a fixed fraction $1-c$ of the optimal observable revenue is collected by time $T=\ln(1/c)/\delta$, independently of the valuation distribution. This is the horizon on which the periodic policy $\hat p$ replays $p$.
--
--   Differences from the source:
--   - generalization: $p$ is the optimal price function of $[SPO_0]$ ("the solution from (3)") → every admissible price function $p$, in additive form; reason: at an optimal $p$ (with $\mathrm{Rev}_0(p)=R_0<\infty$) the Lean statement is the printed one; the paper never proves that an optimal $p$ exists
--   - encoding: $T=\ln(1/c)/\delta$ → hypothesis $0<\delta$; reason: the printed $T$ is defined only for $\delta>0$
--   - encoding: $R_{[0,T]}$ as a Stieltjes integral against $d(1-F(\psi(t)))$ → lower Lebesgue integral over $v\sim F$ of the revenue from purchases at times $\le T$; reason: the same quantity for continuous $p$; defined for every admissible $p$
--   - generalization: valuation cdf $F$ with density $f$ on $[0,\bar v]$ (p.8) → any Borel probability law $F$ with $F([0,\bar v]^c)=0$ (atoms allowed); reason: the paper's instances are special cases; the statement does not use the density
-- source:
--   Correa, Pizarro & Vulcano, The Value of Observing the Buyer Arrival Time in Dynamic Pricing, SSRN 3541494 (rev. Oct 2022), Lemma 1, p.18; proof pp.A5–A6

import Mathlib
import Definitions.Def_ObsArrivalPricing_Model

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ObsArrivalPricing

/-- Lemma 1 (SSRN 3541494, p.18; proof pp.A5–A6), for every admissible price function. For
`c ∈ (0,1)` and `T = ln(1/c)/δ`, the revenue `R_{[0,T]}` collected up to time `T` by an
admissible `p` from a buyer arriving at `0` satisfies `Rev0(p) ≤ R_{[0,T]}(p) + c·R0`. For an
optimal `p` (`Rev0(p) = R0 < ∞`) this is the printed `R_{[0,T]} ≥ (1 − c)R0`. -/
theorem lemma_1 (I : ProblemInstance) (hδ : 0 < I.δ) {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1)
    {p : ℝ → ℝ} (hp : IsAdmissible I.vbar p) :
    Rev0 I.F I.δ I.μ p ≤
      RevUpTo I.F I.δ I.μ p (Real.log (1 / c) / I.δ) +
        ENNReal.ofReal c * R0 I.vbar I.F I.δ I.μ := by sorry

end ObsArrivalPricing
