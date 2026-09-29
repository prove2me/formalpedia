-- Prove2me | Theorems.Thm_OptimalPAC_SampleComplexity_sampleComplexity_le
-- name    : OptimalPAC.SampleComplexity.sampleComplexity_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:31:41.742982+00:00
-- url     : https://prove2.me/theorems/1b0af15c-c3a7-4446-a41e-d7c037caa0a5
-- title:
--   Theorem 2 (Hanneke 2016) — $\mathcal M(\varepsilon,\delta)\le\frac{1800}\varepsilon\left(d+\ln\frac{18}\delta\right)$
-- statement:
--   Let $\mathcal X$ be a measurable space and $\mathbb C$ a concept space of measurable classifiers $\mathcal X\to\{-1,+1\}$ with $|\mathbb C|\ge3$ and finite VC dimension $d$. Assume $\mathbb C$ is well-behaved and admits a measurable sample-consistent learner. Then for all $\varepsilon,\delta\in(0,1)$ the sample complexity of $(\varepsilon,\delta)$-PAC learning $\mathbb C$ in the realizable case satisfies
--   $$\mathcal M(\varepsilon,\delta)\le\frac{1800}\varepsilon\left(d+\ln\left(\frac{18}\delta\right)\right).$$
--   In particular $\mathcal M(\varepsilon,\delta)=O\left(\frac1\varepsilon\left(d+\mathrm{Log}\left(\frac1\delta\right)\right)\right)$ with a numerical constant independent of $\mathbb C$ and $\mathcal X$, which matches the classical lower bound and removes the $\log(1/\varepsilon)$ factor of earlier upper bounds.
--
--   **Formalization Note** Since $\mathcal M(\varepsilon,\delta)\in\mathbb N\cup\{\infty\}$, the bound is stated as $\mathcal M(\varepsilon,\delta)\le\left\lfloor\frac{1800}\varepsilon\left(d+\ln\frac{18}\delta\right)\right\rfloor$, which is equivalent. The constant $1800$ is the paper's $c$ (p. 8); the bound is the last display of the proof (p. 11). $\mathcal M$ is defined over deterministic algorithms that output measurable classifiers; the paper also admits randomized ones, which can only lower $\mathcal M$, so this statement implies the paper's. The two measurability hypotheses are the explicit form of the paper's blanket measurability assumption (p. 3) and hold for every countable class of measurable classifiers.
-- source:
--   Hanneke, The Optimal Sample Complexity of PAC Learning, arXiv:1507.00473v4, p. 7, Theorem 2; explicit form p. 11, last display of the proof (c = 1800, p. 8); Definition 1, p. 2

import Mathlib
import Definitions.Def_OptimalPAC_SampleComplexity_Model

namespace OptimalPAC.SampleComplexity

/-- **Theorem 2** (Hanneke 2016, p. 7), in the explicit form established at the end of its proof
(p. 11) with `c = 1800`: for `ε, δ ∈ (0,1)`,
`𝓜(ε, δ) ≤ (c/ε)(d + ln(18/δ))`, i.e. (since `𝓜` is an integer or `∞`)
`𝓜(ε, δ) ≤ ⌊(1800/ε)(d + ln(18/δ))⌋`. -/
theorem sampleComplexity_le {X : Type*} [MeasurableSpace X] (C : Set (X → Bool))
    (hCm : ∀ h ∈ C, Measurable h) (hC3 : 3 ≤ C.encard) (d : ℕ) (hd : vcDim C = d)
    (hWB : WellBehaved C)
    (hL : ∃ L : List (X × Bool) → X → Bool, IsConsistentLearner C L ∧ LearnerMeasurable L)
    (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    sampleComplexity C ε δ ≤ ((⌊1800 / ε * (d + Real.log (18 / δ))⌋₊ : ℕ) : ℕ∞) := by sorry

end OptimalPAC.SampleComplexity
