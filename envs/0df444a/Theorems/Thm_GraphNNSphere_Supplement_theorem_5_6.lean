-- Prove2me | Theorems.Thm_GraphNNSphere_Supplement_theorem_5_6
-- name    : GraphNNSphere.Supplement.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:59:01.842387+00:00
-- url     : https://prove2.me/theorems/23e5678a-77a7-4b41-8937-cd44b7723d38
-- title:
--   Theorem 5.6, p.69 — restarts: $e^{(\eta^*+\varepsilon)d}$ runs suffice and $S_D(q)=e^{-(\eta^*\pm\varepsilon)d}$
-- statement:
--   Let the data be uniform in either regime, take $k=1$, assume that $\Delta$ lies in the near-threshold band of Section 5.2 (with $\rho=\rho_\beta$, resp. $r_\gamma$), and let $\varepsilon>0$. A run succeeds after its first completed expansion whose evaluated points include the nearest neighbor. There is $c_\varepsilon>0$ such that for all large $n$, every query $q$ fixed before sampling and every integer $B\ge e^{(\eta^*+\varepsilon)d}$:
--
--   1. $B$ independent runs of greedy navigation on $G_\rho$ from uniformly random entries, drawn with replacement, all fail to evaluate the nearest neighbor of $q$ with probability at most $e^{-c_\varepsilon d}$ over the data and the entries;
--   2. with probability at least $1-e^{-c_\varepsilon d}$ over the data, the fraction $S_D(q)$ of entries from which the run evaluates the nearest neighbor satisfies
--
--   $$e^{-(\eta^*+\varepsilon)d}\le S_D(q)\le e^{-(\eta^*-\varepsilon)d}.$$
--
--   The constant $c_\varepsilon$ depends only on $\varepsilon$ and on $(c,\beta)$, resp. $\gamma$, and the bounds are uniform in $q$.
--
--   Conditional on one sample, the number of fresh entries needed is thus governed by the reciprocal of the single-run success probability of Theorem 5.3.
--
--   **Formalization Note** With $k=1$, a run evaluates the nearest neighbor exactly when it succeeds, so failure is $W_G(q;x_0)=\infty$. $c_\varepsilon$ is chosen before the dimension sequence; the threshold before $q$ and $B$.
--
--   Differences from the source:
--   - encoding: O(·), o(1), Ω(d), e^{o(d)}, "with probability 1 − o(1)", "for all sufficiently large n" → explicit constants and vanishing sequences in the quantifier order of §2.1 (fixed parameters, constants, d(·), vanishing sequences, ∀ᶠ n), probabilities as measures of explicit measurable events; reason: Lean convention, as in the published goal Theorem 3.1
--   - encoding: uniform random entry label → uniformOn univ on Fin n, independent of the sample (product measure); reason: same law
--   - encoding: B independent runs from uniform entries drawn with replacement → the product of B uniform label laws, independent of the sample; reason: same law
--   - encoding: S_D(q), the fraction of entries from which the run evaluates the nearest neighbor → #{x₀ : W_G(q; x₀) < ∞}/n with k = 1; reason: with k = 1 success is evaluation of the nearest neighbor
--   - encoding: η* in the logarithmic regime and the band → etaStarLog and InBandLog at the limiting angles; reason: as for Theorem 5.3
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 5.6, p.69 (PDF p.71); band §5.2, p.60

import Mathlib
import Definitions.Def_GraphNNSphere_rhoBeta
import Definitions.Def_GraphNNSphere_rGamma
import Definitions.Def_GraphNNSphere_dataLaw
import Definitions.Def_GraphNNSphere_W
import Definitions.Def_GraphNNSphere_thresholdGraph
import Definitions.Def_GraphNNSphere_nnGraph
import Definitions.Def_GraphNNSphere_logDim
import Definitions.Def_GraphNNSphere_IsDenseRegime
import Definitions.Def_GraphNNSphere_Supplement_etaStarDense
import Definitions.Def_GraphNNSphere_Supplement_etaStarLog

open MeasureTheory Filter Topology ProbabilityTheory

namespace GraphNNSphere

namespace Supplement

open Classical in
/-- Theorem 5.6, restarts (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 5.6, p.69). Uniform data, either regime, `k = 1`, `Δ` in the
near-threshold band, `ε > 0`. There is `c_ε > 0` such that for all large `n`, every query `q` fixed before
sampling and every integer `B ≥ e^{(η*+ε)d}`, `B` independent runs of greedy navigation on `G_ρ` from
uniform entries drawn with replacement all fail to evaluate the nearest neighbor of `q` with
probability at most `e^{-c_ε d}` over the data and the entries; and with probability at least
`1 - e^{-c_ε d}` over the data, the fraction `S_D(q)` of entries from which the run evaluates the nearest
neighbor satisfies `e^{-(η*+ε)d} ≤ S_D(q) ≤ e^{-(η*-ε)d}`. `c_ε` depends only on `ε` and `(c, β)`, resp. `γ`,
and the bounds are uniform in `q`.

**Formalization Note** With `k = 1` a run evaluates the nearest neighbor exactly when it succeeds, so
failure is `W = ⊤` and `S_D(q) = #{x₀ : W < ⊤}/n`. `c_ε` comes before `d(·)`; the threshold comes before
`q` and `B`. `ρ = ρ_β`, resp. `r_γ`. -/
theorem theorem_5_6 :
    (∀ c β ε : ℝ, 0 < c → InBandLog c β → 0 < ε →
      ∃ cε : ℝ, 0 < cε ∧ ∀ᶠ n : ℕ in atTop, ∀ q : Sph (logDim c n),
        (∀ B : ℕ, Real.exp ((etaStarLog c β + ε) * (logDim c n : ℝ)) ≤ (B : ℝ) →
          ((dataLaw n (logDim c n)).prod
              (Measure.pi (fun _ : Fin B => uniformOn (Set.univ : Set (Fin n)))))
            {p | ∀ b : Fin B, W (thresholdGraph p.1 (rhoBeta n (logDim c n) β)) p.1 q 1 (p.2 b) = ⊤} ≤
            ENNReal.ofReal (Real.exp (-(cε * (logDim c n : ℝ))))) ∧
        ∃ Ev : Set (Fin n → Sph (logDim c n)), MeasurableSet Ev ∧
          1 - Real.exp (-(cε * (logDim c n : ℝ))) ≤ (dataLaw n (logDim c n) Ev).toReal ∧
          ∀ X ∈ Ev,
            Real.exp (-((etaStarLog c β + ε) * (logDim c n : ℝ))) ≤
              ((Finset.univ.filter (fun x₀ : Fin n =>
                W (thresholdGraph X (rhoBeta n (logDim c n) β)) X q 1 x₀ < ⊤)).card : ℝ) / n ∧
            ((Finset.univ.filter (fun x₀ : Fin n =>
                W (thresholdGraph X (rhoBeta n (logDim c n) β)) X q 1 x₀ < ⊤)).card : ℝ) / n ≤
              Real.exp (-((etaStarLog c β - ε) * (logDim c n : ℝ)))) ∧
    (∀ γ ε : ℝ, InBandDense γ → 0 < ε →
      ∃ cε : ℝ, 0 < cε ∧ ∀ d : ℕ → ℕ, IsDenseRegime d → ∀ᶠ n : ℕ in atTop, ∀ q : Sph (d n),
        (∀ B : ℕ, Real.exp ((etaStarDense γ + ε) * (d n : ℝ)) ≤ (B : ℝ) →
          ((dataLaw n (d n)).prod
              (Measure.pi (fun _ : Fin B => uniformOn (Set.univ : Set (Fin n)))))
            {p | ∀ b : Fin B, W (thresholdGraph p.1 (rGamma n (d n) γ)) p.1 q 1 (p.2 b) = ⊤} ≤
            ENNReal.ofReal (Real.exp (-(cε * (d n : ℝ))))) ∧
        ∃ Ev : Set (Fin n → Sph (d n)), MeasurableSet Ev ∧
          1 - Real.exp (-(cε * (d n : ℝ))) ≤ (dataLaw n (d n) Ev).toReal ∧
          ∀ X ∈ Ev,
            Real.exp (-((etaStarDense γ + ε) * (d n : ℝ))) ≤
              ((Finset.univ.filter (fun x₀ : Fin n =>
                W (thresholdGraph X (rGamma n (d n) γ)) X q 1 x₀ < ⊤)).card : ℝ) / n ∧
            ((Finset.univ.filter (fun x₀ : Fin n =>
                W (thresholdGraph X (rGamma n (d n) γ)) X q 1 x₀ < ⊤)).card : ℝ) / n ≤
              Real.exp (-((etaStarDense γ - ε) * (d n : ℝ)))) := by sorry

end Supplement

end GraphNNSphere
