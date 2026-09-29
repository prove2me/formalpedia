-- Prove2me | Theorems.Thm_OptimalPAC_SampleComplexity_hanneke_learner_pac
-- name    : OptimalPAC.SampleComplexity.hanneke_learner_pac
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:31:09.153984+00:00
-- url     : https://prove2.me/theorems/b1bc7e99-aa81-429c-89d8-331eb0070a0d
-- title:
--   Sample size (10) — $\mathrm{Majority}(L(\mathbb A(\cdot;\emptyset)))$ is $(\varepsilon,\delta)$-PAC from $\left\lfloor\frac{1800}\varepsilon\left(d+\ln\frac{18}\delta\right)\right\rfloor$ samples
-- statement:
--   Let $\mathbb C$ be a well-behaved concept space of measurable classifiers with $|\mathbb C|\ge3$ and finite VC dimension $d$, and let $L$ be a measurable sample-consistent learner for $\mathbb C$. Let $\mathcal P$ be a probability measure on $\mathcal X$, $f^\star\in\mathbb C$ and $\varepsilon,\delta\in(0,1)$. For every integer
--   $$m\ge\left\lfloor\frac{1800}\varepsilon\left(d+\ln\left(\frac{18}\delta\right)\right)\right\rfloor,$$
--   if $X_1,\ldots,X_m$ are independent with law $\mathcal P$, then with probability at least $1-\delta$ the classifier $\hat h=\mathrm{Majority}(L(\mathbb A(\{(X_i,f^\star(X_i))\}_{i=1}^m;\emptyset)))$ satisfies
--   $$\mathrm{er}_{\mathcal P}(\hat h;f^\star)\le\varepsilon.$$
--
--   This is the algorithmic content of Theorem 2: a single, explicit learner attains the optimal sample complexity for every distribution and every target.
--
--   **Formalization Note** The failure event $\mathrm{er}>\varepsilon$ is bounded in outer measure by $\delta$. The measurability hypotheses are as in claim (9).
-- source:
--   Hanneke, The Optimal Sample Complexity of PAC Learning, arXiv:1507.00473v4, proof of Theorem 2, p. 11, eq. (10) (with T = ∅ in (9))

import Mathlib
import Definitions.Def_OptimalPAC_SampleComplexity_Model
import Definitions.Def_OptimalPAC_SampleComplexity_Algorithm

open MeasureTheory

namespace OptimalPAC.SampleComplexity

/-- The sample size (10) (Hanneke 2016, p. 11), with `c = 1800` and `T = ∅`: for
`ε, δ ∈ (0,1)` and every `m ≥ ⌊(c/ε)(d + ln(18/δ))⌋`, the learner
`Majority(L(𝔸(·; ∅)))` has error at most `ε` with probability at least `1 − δ`. -/
theorem hanneke_learner_pac {X : Type*} [MeasurableSpace X] (C : Set (X → Bool))
    (hCm : ∀ h ∈ C, Measurable h) (hC3 : 3 ≤ C.encard) (d : ℕ) (hd : vcDim C = d)
    (hWB : WellBehaved C)
    (L : List (X × Bool) → X → Bool) (hL : IsConsistentLearner C L) (hLm : LearnerMeasurable L)
    (P : Measure X) [IsProbabilityMeasure P] (f : X → Bool) (hf : f ∈ C)
    (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : ⌊1800 / ε * (d + Real.log (18 / δ))⌋₊ ≤ m) :
    Measure.pi (fun _ : Fin m => P)
      {x | ε < er P (hannekeLearner L (labeled f x) []) f}
      ≤ ENNReal.ofReal δ := by sorry

end OptimalPAC.SampleComplexity
