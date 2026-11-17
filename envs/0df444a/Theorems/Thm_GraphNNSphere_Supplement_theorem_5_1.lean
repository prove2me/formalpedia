-- Prove2me | Theorems.Thm_GraphNNSphere_Supplement_theorem_5_1
-- name    : GraphNNSphere.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:55:27.974387+00:00
-- url     : https://prove2.me/theorems/1cfbba04-f15a-4558-98e2-af9e4ee1ce8b
-- title:
--   Theorem 5.1, p.54 — fresh starts cost $e^{(\gamma+\eta^*(\gamma)\pm o(1))d}$ evaluations
-- statement:
--   Let the data be uniform in the dense regime, fix $k\ge1$ and $\tfrac12\log(4/3)\le\gamma<\gamma_c$, let $\Delta=\lceil e^{\gamma d}\rceil$, and let $\eta^*(\gamma)$ be the exponent (50). Fix a query $q$ before sampling; success probabilities are averaged over the sample and the algorithm's random choices.
--
--   1. On either $G_{r_\gamma}$ or $N_\Delta$, every local exploration algorithm with data-independent entries requires at least $e^{(\gamma+\eta^*(\gamma)-o(1))d}$ distinct evaluations to succeed with probability bounded away from zero.
--   2. Independent restarts from uniform random entries on $G_{r_\gamma}$, all using the same sample, succeed with probability tending to one using at most $e^{(\gamma+\eta^*(\gamma)+o(1))d}$ distinct evaluations.
--   3. The minimum of $\gamma+\eta^*(\gamma)$ over $[\tfrac12\log(4/3),\gamma_c)$ is attained at $e^{2\gamma}=(12+2\sqrt3)/11$ and is approximately $0.243$, compared with the every-entry exponent $\gamma_c\approx0.347$.
--
--   Thus relaxing the every-entry guarantee to fresh random starts lowers the exponential cost from $e^{\gamma_c d}$ to $e^{0.243\ldots d}$, and no adaptive local exploration does better than independent restarts.
--
--   **Formalization Note** In (1), for every success level $p>0$ there is $\delta_n\to0$ such that for all large $n$ no measurable algorithm reaches a target within $e^{(\gamma+\eta^*-\delta_n)d}$ distinct evaluations with probability $\ge p$. In (2) the restart entries are an i.i.d. uniform label sequence independent of the sample (infinite product measure). The query is a sequence $q_n$ fixed before the vanishing terms.
--
--   Differences from the source:
--   - encoding: O(·), o(1), Ω(d), e^{o(d)}, "with probability 1 − o(1)", "for all sufficiently large n" → explicit constants and vanishing sequences in the quantifier order of §2.1 (fixed parameters, constants, d(·), vanishing sequences, ∀ᶠ n), probabilities as measures of explicit measurable events; reason: Lean convention, as in the published goal Theorem 3.1
--   - generalization: local exploration algorithms whose entry labels follow a sequence fixed before sampling or are drawn afresh uniformly → algorithms whose j-th entry label is any function of the internal randomness (and whose operations are measurable); reason: conditioning on the randomness turns such an algorithm into one with a fixed sequence; the bound, uniform over algorithms, passes to the average, so the Lean statement specializes to the source
--   - encoding: every local exploration algorithm (probabilities over the data and its randomness) → algorithms with a probability space (Ω, μ) of internal randomness and measurable induced operations (IsMeasurableExplorer); reason: the probabilities in the statement are only defined for measurable algorithms; Theorem 5.9 names the requirement
--   - encoding: uniform random entry label → uniformOn univ on Fin n, independent of the sample (product measure); reason: same law
--   - encoding: "requires at least e^{(γ+η*−o(1))d} distinct evaluations to succeed with probability bounded away from zero" → ∀ p > 0 ∃ δ_n → 0, eventually, ∀ algorithm: P(V ≤ e^{(γ+η*−δ_n)d}) < p; reason: the meaning of the asymptotic claim
--   - encoding: independent restarts from uniform random entries → an i.i.d. uniform label sequence (Measure.infinitePi), cost = labels evaluated by all attempts through the first success; reason: §1.2, p.3 cost convention
--   - reading: "approximately 0.243", "γ_c ≈ 0.347" → 0.2425 ≤ min < 0.2435 and 0.3465 ≤ γ_c < 0.3475; reason: rounding to three decimals (true values 0.24299 and 0.34657)
--   - encoding: "attained at e^{2γ} = (12 + 2√3)/11" → that γ lies in the band and minimizes γ + η*(γ) there; reason: uniqueness is not claimed
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 5.1, p.54 (PDF p.56); η*(γ) Eq. (50), p.54

import Mathlib
import Definitions.Def_GraphNNSphere_rGamma
import Definitions.Def_GraphNNSphere_dataLaw
import Definitions.Def_GraphNNSphere_thresholdGraph
import Definitions.Def_GraphNNSphere_nnGraph
import Definitions.Def_GraphNNSphere_IsDenseRegime
import Definitions.Def_GraphNNSphere_Supplement_etaStarDense
import Definitions.Def_GraphNNSphere_Supplement_LocalExplorer
import Definitions.Def_GraphNNSphere_Supplement_restartCost

open MeasureTheory Filter Topology ProbabilityTheory

namespace GraphNNSphere

namespace Supplement

/-- Theorem 5.1, the evaluation cost of fresh starts (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 5.1, p.54). Uniform data, dense
regime, `½ log(4/3) ≤ γ < γ_c`, `Δ = ⌈e^{γd}⌉`, a query `q` fixed before sampling. (i) On `G_{r_γ}` or `N_Δ`,
every local exploration algorithm with data-independent entries needs at least
`e^{(γ+η*(γ)-o(1))d}` distinct evaluations to succeed with probability bounded away from zero.
(ii) Independent restarts from uniform random entries on `G_{r_γ}`, all on one sample, succeed with
probability tending to one using at most `e^{(γ+η*(γ)+o(1))d}` distinct evaluations. (iii) The minimum
of `γ + η*(γ)` over `[½ log(4/3), γ_c)` is attained at `e^{2γ} = (12 + 2√3)/11` and is approximately
`0.243`, compared with `γ_c ≈ 0.347`.

**Formalization Note** (i): for every success level `p > 0` there is `δ_n → 0` such that for all large
`n` no measurable algorithm reaches a target with at most `e^{(γ+η*-δ_n)d}` distinct evaluations with
probability `≥ p`. (ii): the restart entries are an i.i.d. uniform label sequence (infinite product),
independent of the sample; the cost counts all labels evaluated by all attempts through the
successful one. The query is a sequence `q_n` fixed before the `o(1)` terms. (iii): "approximately
`0.243`" is `0.2425 ≤ min < 0.2435`, "`γ_c ≈ 0.347`" is `0.3465 ≤ γ_c < 0.3475`. -/
theorem theorem_5_1 :
    (∀ k : ℕ, 1 ≤ k → ∀ γ : ℝ, InBandDense γ → ∀ d : ℕ → ℕ, IsDenseRegime d →
      ∀ q : ∀ n, Sph (d n), ∀ nn : Bool, ∀ p : ℝ, 0 < p →
      ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (A : LocalExplorer n (d n) Ω),
          IsMeasurableExplorer (fun X => if nn then nnGraph X ⌈Real.exp (γ * (d n : ℝ))⌉₊
            else thresholdGraph X (rGamma n (d n) γ)) (q n) k A →
          ((dataLaw n (d n)).prod μ)
            {ω' | ∃ m : ℕ, explCost (if nn then nnGraph ω'.1 ⌈Real.exp (γ * (d n : ℝ))⌉₊
                else thresholdGraph ω'.1 (rGamma n (d n) γ)) ω'.1 (q n) k A ω'.2 ⊤ ⊤ = m ∧
              (m : ℝ) ≤ Real.exp ((γ + etaStarDense γ - δ n) * (d n : ℝ))} <
            ENNReal.ofReal p) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ γ : ℝ, InBandDense γ → ∀ d : ℕ → ℕ, IsDenseRegime d →
      ∀ q : ∀ n, Sph (d n),
      ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
        Tendsto (fun n : ℕ => ((dataLaw n (d n)).prod
            (Measure.infinitePi (fun _ : ℕ => (uniformOn (Set.univ : Set (Fin n))))))
            {ω' | ∃ m : ℕ, restartCost (thresholdGraph ω'.1 (rGamma n (d n) γ)) ω'.1 (q n) k ω'.2 = m ∧
              (m : ℝ) ≤ Real.exp ((γ + etaStarDense γ + δ n) * (d n : ℝ))})
          atTop (𝓝 1)) ∧
    (InBandDense (Real.log ((12 + 2 * Real.sqrt 3) / 11) / 2) ∧
      (∀ γ : ℝ, InBandDense γ →
        Real.log ((12 + 2 * Real.sqrt 3) / 11) / 2 +
            etaStarDense (Real.log ((12 + 2 * Real.sqrt 3) / 11) / 2) ≤ γ + etaStarDense γ) ∧
      0.2425 ≤ Real.log ((12 + 2 * Real.sqrt 3) / 11) / 2 +
            etaStarDense (Real.log ((12 + 2 * Real.sqrt 3) / 11) / 2) ∧
      Real.log ((12 + 2 * Real.sqrt 3) / 11) / 2 +
            etaStarDense (Real.log ((12 + 2 * Real.sqrt 3) / 11) / 2) < 0.2435 ∧
      0.3465 ≤ gammaC ∧ gammaC < 0.3475) := by sorry

end Supplement

end GraphNNSphere
