-- Prove2me | Theorems.Thm_OptimalPAC_SampleComplexity_majority_subsample_error_bound
-- name    : OptimalPAC.SampleComplexity.majority_subsample_error_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:30:22.484983+00:00
-- url     : https://prove2.me/theorems/c4b580ef-c9a7-44cd-abb9-a8abd0b051da
-- title:
--   Claim (9) — $\mathrm{er}(\hat h_{m,T})\le\frac{1800}{m+1}\left(d+\ln\frac{18}\delta\right)$ with probability $1-\delta$
-- statement:
--   Let $\mathbb C$ be a well-behaved concept space of measurable classifiers with $|\mathbb C|\ge3$ and finite VC dimension $d$, and let $L$ be a measurable sample-consistent learner for $\mathbb C$. Let $\mathcal P$ be a probability measure on $\mathcal X$, $f^\star\in\mathbb C$, $m\ge1$, $\delta\in(0,1)$, and let $T$ be a finite sequence in $\mathcal X\times\mathcal Y$ with $f^\star\in\mathbb C[T]$. Let $\mathbb S_{1:m}=\{(X_i,f^\star(X_i))\}_{i=1}^m$ with $X_1,\ldots,X_m$ independent with law $\mathcal P$, and $\hat h_{m,T}=\mathrm{Majority}(L(\mathbb A(\mathbb S_{1:m};T)))$. Then with probability at least $1-\delta$,
--   $$\mathrm{er}_{\mathcal P}(\hat h_{m,T};f^\star)\le\frac{1800}{m+1}\left(d+\ln\left(\frac{18}\delta\right)\right).$$
--
--   This is the statement proved by induction on $m$ in the proof of Theorem 2 (claim (5) for every $m'$), with the numerical constant $c=1800$.
--
--   **Formalization Note** The failure event is bounded in outer measure. The hypotheses "well-behaved" and "measurable learner" make explicit the paper's measurability assumption (p. 3); both hold for every countable class of measurable classifiers.
-- source:
--   Hanneke, The Optimal Sample Complexity of PAC Learning, arXiv:1507.00473v4, proof of Theorem 2, p. 11, eq. (9) (claim (5), p. 8, with c = 1800)

import Mathlib
import Definitions.Def_OptimalPAC_SampleComplexity_Model
import Definitions.Def_OptimalPAC_SampleComplexity_Algorithm

open MeasureTheory

namespace OptimalPAC.SampleComplexity

/-- **Claim (9)** of the proof of Theorem 2 (Hanneke 2016, p. 11), with `c = 1800`: for every
`m ≥ 1`, `δ ∈ (0,1)` and finite sequence `T` with `f⋆ ∈ ℂ[T]`, with probability at least
`1 − δ` the classifier `ĥ_{m,T} = Majority(L(𝔸(𝕊_{1:m}; T)))` satisfies
`er_P(ĥ_{m,T}; f⋆) ≤ (c/(m+1))(d + ln(18/δ))`. -/
theorem majority_subsample_error_bound {X : Type*} [MeasurableSpace X] (C : Set (X → Bool))
    (hCm : ∀ h ∈ C, Measurable h) (hC3 : 3 ≤ C.encard) (d : ℕ) (hd : vcDim C = d)
    (hWB : WellBehaved C)
    (L : List (X × Bool) → X → Bool) (hL : IsConsistentLearner C L) (hLm : LearnerMeasurable L)
    (P : Measure X) [IsProbabilityMeasure P] (f : X → Bool) (hf : f ∈ C)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (T : List (X × Bool)) (hT : ∀ p ∈ T, f p.1 = p.2) :
    Measure.pi (fun _ : Fin m => P)
      {x | 1800 / ((m : ℝ) + 1) * (d + Real.log (18 / δ)) <
        er P (hannekeLearner L (labeled f x) T) f}
      ≤ ENNReal.ofReal δ := by sorry

end OptimalPAC.SampleComplexity
