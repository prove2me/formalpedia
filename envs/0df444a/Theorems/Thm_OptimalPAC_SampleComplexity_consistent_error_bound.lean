-- Prove2me | Theorems.Thm_OptimalPAC_SampleComplexity_consistent_error_bound
-- name    : OptimalPAC.SampleComplexity.consistent_error_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:27:04.793924+00:00
-- url     : https://prove2.me/theorems/39b66463-b8a8-4d6b-9212-a8e0684e805f
-- title:
--   Lemma 4 — error bound $\frac2m\left(d\,\mathrm{Log}_2\frac{2em}{d}+\mathrm{Log}_2\frac2\delta\right)$ for sample-consistent classifiers
-- statement:
--   Let $\mathbb C$ be a concept space of measurable classifiers with $|\mathbb C|\ge3$ and finite VC dimension $d$, and assume $\mathbb C$ is well-behaved. Let $\delta\in(0,1)$, $m\ge1$, $f^\star\in\mathbb C$, and let $P$ be a probability measure on $\mathcal X$. If $Z_1,\ldots,Z_m$ are independent with law $P$, then with probability at least $1-\delta$ every $h\in\mathbb C[\{(Z_i,f^\star(Z_i))\}_{i=1}^m]$ satisfies
--   $$\mathrm{er}_P(h;f^\star)\le\frac2m\left(d\,\mathrm{Log}_2\left(\frac{2em}{d}\right)+\mathrm{Log}_2\left(\frac2\delta\right)\right),$$
--   where $\mathrm{Log}_2(z)=\log_2(\max\{z,2\})$.
--
--   This is the classical generalization bound for sample-consistent classifiers of Blumer, Ehrenfeucht, Haussler and Warmuth (1989), which the paper imports without proof; the proof of Theorem 2 applies it under conditional distributions $P(\cdot\mid\mathrm{ER}(h_i))$.
--
--   **Formalization Note** The statement bounds the outer measure of the failure event "some consistent $h$ has error larger than the bound" by $\delta$. The well-behavedness hypothesis is the explicit form of the paper's measurability assumption (p. 3), which the paper says comes into effect only in this lemma; without it the lemma fails for some classes of VC dimension 1. The standing assumptions $|\mathbb C|\ge3$ (hence $d\ge1$) and measurable classifiers are carried as hypotheses.
-- source:
--   Hanneke, The Optimal Sample Complexity of PAC Learning, arXiv:1507.00473v4, p. 8, Lemma 4 (footnote 4, p. 7: Blumer et al. 1989, Theorem A2.1 and Proposition A2.1)

import Mathlib
import Definitions.Def_OptimalPAC_SampleComplexity_Model

open MeasureTheory

namespace OptimalPAC.SampleComplexity

/-- **Lemma 4** (Hanneke 2016, p. 8; Blumer, Ehrenfeucht, Haussler and Warmuth 1989): for
`δ ∈ (0,1)`, `m ≥ 1`, `f⋆ ∈ C` and any probability measure `P`, with probability at least
`1 − δ` over `Z₁, …, Z_m` i.i.d. `P`, every `h ∈ ℂ[{(Z_i, f⋆(Z_i))}]` has
`er_P(h; f⋆) ≤ (2/m)(d Log₂(2em/d) + Log₂(2/δ))`. Stated as a bound on the (outer) measure of
the failure event. -/
theorem consistent_error_bound {X : Type*} [MeasurableSpace X] (C : Set (X → Bool))
    (hCm : ∀ h ∈ C, Measurable h) (hC3 : 3 ≤ C.encard) (d : ℕ) (hd : vcDim C = d)
    (hWB : WellBehaved C)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (m : ℕ) (hm : 1 ≤ m) (f : X → Bool) (hf : f ∈ C)
    (P : Measure X) [IsProbabilityMeasure P] :
    Measure.pi (fun _ : Fin m => P)
      {z | ∃ h ∈ consistent C (labeled f z),
        2 / (m : ℝ) * ((d : ℝ) * Log2 (2 * Real.exp 1 * m / d) + Log2 (2 / δ)) < er P h f}
      ≤ ENNReal.ofReal δ := by sorry

end OptimalPAC.SampleComplexity
