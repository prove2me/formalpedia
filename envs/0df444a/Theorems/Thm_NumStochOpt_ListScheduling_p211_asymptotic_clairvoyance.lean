-- Prove2me | Theorems.Thm_NumStochOpt_ListScheduling_p211_asymptotic_clairvoyance
-- name    : NumStochOpt.ListScheduling.p211_asymptotic_clairvoyance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T21:12:36.746985+00:00
-- url     : https://prove2.me/theorems/2f746cea-960a-4a0a-9730-fda4dadc212d
-- title:
--   p. 211 — asymptotic clairvoyance of the two-stage heuristic $m^{H1}$ + list scheduling
-- statement:
--   Let $p_1, p_2, \dots$ be independent, identically distributed, nonnegative processing times with mean $\mu > 0$ and $\mathbb E p_1^2 < \infty$, and let each machine cost $c > 0$. The two-stage heuristic buys $m^{H1}_n$ machines, the better of $\lfloor\sqrt{n\mu/c}\rfloor$ and $\lceil\sqrt{n\mu/c}\rceil$ for $Z'_n(m) = cm + n\mu/m$, and then schedules the $n$ jobs by list scheduling, with makespan $C^{H2}_n(m^{H1}_n)$. A clairvoyant decision maker who knows the processing times in advance chooses $m^\circ_n(\omega) \ge 1$ with
--
--   $$
--   c\, m^\circ_n + C^*_n(m^\circ_n) = \min_{m \ge 1} \bigl\{ cm + C^*_n(m) \bigr\}.
--   $$
--
--   Then almost surely
--
--   $$
--   \lim_{n\to\infty} \frac{c\, m^{H1}_n + C^{H2}_n(m^{H1}_n)}{c\, m^\circ_n + C^*_n(m^\circ_n)} = 1 .
--   $$
--
--   The relative error attributable to imperfect information vanishes almost surely; Lenstra et al. call this property **asymptotic clairvoyance**. The book gives no proof beyond "the reasoning used for the justification of result (8.13)".
--
--   **Formalization Note** $m^\circ_n$ is any function `mo : ℕ → Ω → ℕ` with `mo n ω ≥ 1` that minimizes $cm + C^*_n(m)$ over $m \ge 1$ for each realization; no measurability of `mo` is assumed. The book minimizes over $m \in \mathbb N$; $m = 0$ (no machine, which cannot process any job) is excluded, since the Lean value of $C^*_n(0)$ for $n \ge 1$ is the empty-infimum convention $0$, not a makespan. $m^{H1}_n$ is `firstStageMachines c μ n` (ties go to the floor; the ceiling when the floor is $0$).
-- source:
--   A. H. G. Rinnooy Kan, L. Stougie, "Stochastic Integer Programming", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 8, §8.3, p. 211, unnumbered display (asymptotic clairvoyance); m^{H1}: p. 210

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_Makespan
import Definitions.Def_NumStochOpt_ListScheduling_ListSchedule
import Definitions.Def_NumStochOpt_ListScheduling_FirstStage

open MeasureTheory ProbabilityTheory Filter Topology

namespace NumStochOpt.ListScheduling

/-- p. 211, asymptotic clairvoyance: under the model of §8.2 (i.i.d. nonnegative processing
times with mean `μ > 0` and `E p₁² < ∞`) and machine cost `c > 0`, let `m^{H1}_n` be the
heuristic first-stage decision and `m°_n(ω) ≥ 1` a machine count minimizing
`c m + C*_n(m)` over `m ≥ 1` for the realized processing times. Then almost surely
`(c m^{H1} + C^{H2}_n(m^{H1})) / (c m°_n + C*_n(m°_n)) → 1`, where `C^{H2}` is the
list-scheduling makespan. -/
theorem p211_asymptotic_clairvoyance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (p : ℕ → Ω → ℝ) (hmeas : ∀ j, Measurable (p j))
    (hindep : iIndepFun p P) (hident : ∀ j, IdentDistrib (p j) (p 0) P P)
    (hnonneg : ∀ j ω, 0 ≤ p j ω) (hsq : Integrable (fun ω => p 0 ω ^ 2) P)
    (μ : ℝ) (hmean : ∫ ω, p 0 ω ∂P = μ) (hμ : 0 < μ)
    (c : ℝ) (hc : 0 < c) (mo : ℕ → Ω → ℕ) (hmo : ∀ n ω, 1 ≤ mo n ω)
    (hmo_opt : ∀ n ω, ∀ k : ℕ, 1 ≤ k →
      c * mo n ω + optMakespan n (mo n ω) (fun j => p j ω)
        ≤ c * k + optMakespan n k (fun j => p j ω)) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ =>
        (c * firstStageMachines c μ n
            + listMakespan n (firstStageMachines c μ n) (fun j => p j ω))
          / (c * mo n ω + optMakespan n (mo n ω) (fun j => p j ω)))
      atTop (𝓝 1) := by sorry

end NumStochOpt.ListScheduling
