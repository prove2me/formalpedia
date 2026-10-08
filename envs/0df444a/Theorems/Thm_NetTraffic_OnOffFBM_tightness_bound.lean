-- Prove2me | Theorems.Thm_NetTraffic_OnOffFBM_tightness_bound
-- name    : NetTraffic.OnOffFBM.tightness_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:45.518356+00:00
-- url     : https://prove2.me/theorems/0d651ebb-d840-4a11-a9a7-8a5403d13f99
-- title:
--   §7.2, p. 63 — E|d_T^{−1} Σ_m G^{(m)}_{Tu}|² ≤ (const) u^{1+ε} for small u > 0 and T ≥ T*
-- statement:
--   Consider the superposition of $M=M(T)$ independent stationary ON/OFF sources with period laws satisfying (2.1)–(2.2), $M$ non-decreasing with $M(T)\to\infty$, and assume Fast Growth Condition 2. Then there are $\varepsilon>0$, a constant $c$, $u_0>0$ and $T^*$ such that for all $T\ge T^*$ and $0<u\le u_0$,
--   $$E\Big|d_T^{-1}\sum_{m=1}^MG^{(m)}_{Tu}\Big|^2\le c\,u^{1+\varepsilon}.$$
--
--   By stationarity of the increments this moment bound controls the increments of the normalised input process and yields tightness in $\mathbb C[0,K]$ for every $K>0$ through Billingsley's moment criterion; it is the step from finite-dimensional to functional convergence in Theorem 4.
--
--   **Formalization Note** "For small $u>0$" is rendered as "for $0<u\le u_0$ with some $u_0>0$"; $c$, $\varepsilon$, $u_0$ and $T^*$ may depend on the model (the laws and $M$) but not on $T$ or $u$.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 63, §7.2, display 'E|d_T^{−1} Σ G^{(m)}_{Tu}|² ≤ (const) u^{1+ε}'

import Mathlib
import Definitions.Def_NetTraffic_OnOffFBM_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NetTraffic.OnOffFBM

/-- §7.2, p. 63: under Condition 2 there are `ε > 0`, a constant `c`, `u_0 > 0` and `T^*` with
`E|d_T^{-1} Σ_{m=1}^M G^{(m)}_{Tu}|² ≤ c u^{1+ε}` for all `0 < u ≤ u_0` and `T ≥ T^*`. -/
theorem tightness_bound
    (Fon Foff : Measure ℝ) [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    (α αoff : ℝ) (hF : HeavyTails Fon Foff α αoff)
    (M : ℝ → ℕ) (hM : SourceCount M) (hC2 : Condition2 Fon M)
    (Ω : ℝ → Type*) [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (src : ∀ T, ℕ → Source (Ω T))
    (hmodel : ∀ T, IsOnOffSuperposition (P T) Fon Foff (M T) (src T)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, ∃ u₀ : ℝ, 0 < u₀ ∧ ∃ Tstar : ℝ, ∀ T, Tstar ≤ T →
      ∀ u : ℝ, 0 < u → u ≤ u₀ →
        (P T)[fun ω => |(dT Fon α M T)⁻¹ *
          ∑ m ∈ Finset.range (M T), (src T m).G (P T) (T * u) ω| ^ 2] ≤ c * u ^ (1 + ε) := by sorry

end NetTraffic.OnOffFBM
