-- Prove2me | Theorems.Thm_KleywegtSAA_ExpRate_union_bound
-- name    : KleywegtSAA.ExpRate.union_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:04:18.468081+00:00
-- url     : https://prove2.me/theorems/c9e021a3-062e-4d21-8df9-8fe701aa369e
-- title:
--   §2.2, p. 4 — 1 − P(Ŝ^ε_N ⊂ 𝒮^ε) ≤ Σ_{x∈𝒮} P{|ĝ_N(x) − g(x)| ≥ α(ε)/2}
-- statement:
--   Let $\mathcal S$ be a nonempty finite set, $(\Omega, P)$ a probability space carrying the sample $W^1, W^2, \dots$, $\varepsilon \ge 0$, and suppose $\mathcal S \setminus \mathcal S^\varepsilon$ is nonempty. Then for every sample size $N$,
--   $$1 - P\big(\hat{\mathcal S}^\varepsilon_N \subset \mathcal S^\varepsilon\big) \le \sum_{x \in \mathcal S} P\big\{ |\hat g_N(x) - g(x)| \ge \alpha(\varepsilon)/2 \big\}.$$
--
--   The bound reduces the failure probability of the SAA method to finitely many one-dimensional deviation probabilities, each controlled by the large-deviations bound (2.4).
--
--   **Formalization Note** The statement holds for any sample sequence, so independence, identical distribution, measurability and integrability are omitted (a stronger statement). Probabilities are values of the measure in $[0,\infty]$, with truncated subtraction $1 - P(\cdot)$; for a probability measure this is the usual complement probability.
-- source:
--   Kleywegt & Shapiro, The sample average approximation method for stochastic discrete optimization, preprint (two-author version, sha256 56657748…), p. 4, §2.2, display after "it follows that"

import Mathlib
import Definitions.Def_KleywegtSAA_ExpRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace KleywegtSAA.ExpRate

/-- §2.2, p. 4: `1 − P(Ŝ^ε_N ⊂ S^ε) ≤ ∑_{x ∈ S} P{|ĝ_N(x) − g(x)| ≥ α(ε)/2}` for every sample
size `N`. -/
theorem union_bound {X : Type*} (S : Finset X) (hS : S.Nonempty)
    {𝒲 : Type*} (G : X → 𝒲 → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (W : ℕ → Ω → 𝒲)
    (ε : ℝ) (hε : 0 ≤ ε) (hne : (nonOptSet S hS (trueObj G P W) ε).Nonempty) :
    ∀ N : ℕ,
      1 - P {ω | epsSet S hS (sampleObj G W N ω) ε ⊆ epsSet S hS (trueObj G P W) ε} ≤
        ∑ x ∈ S, P {ω | alpha S hS (trueObj G P W) ε hne / 2 ≤
          |sampleObj G W N ω x - trueObj G P W x|} := by sorry

end KleywegtSAA.ExpRate
