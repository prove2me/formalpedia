-- Prove2me | Theorems.Thm_MNLTrisection_Adaptive_eq_S33
-- name    : MNLTrisection.Adaptive.eq_S33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:40.121605+00:00
-- url     : https://prove2.me/theorems/fc240b27-9f8f-49bf-ba27-49a5e21d85da
-- title:
--   Eq. (S33), Supplement p. 7 (PDF 26) — a false detection y > F(y) within n_τ explorations has probability ≲ n_τ/T ≲ ln(Tε_τ²)/(Tε_τ²)
-- statement:
--   Let $X_1, X_2, \dots$ be i.i.d. with values in $[0,1]$ and mean $\mu$, let $\rho_\ell = X_1 + \dots + X_\ell$, and let $y \le \mu$. With $\varepsilon_\tau = \tfrac13(\tfrac23)^\tau$ and $n_\tau = 8\lceil \varepsilon_\tau^{-2}\ln(8T\varepsilon_\tau^2)\rceil$, there is a universal constant $C > 0$ such that for every $T \ge 25$ and every epoch $\tau$ with $\sum_{\tau'<\tau} n_{\tau'} < T$,
--   $$\Pr\Big[\exists \ell \in \{1,\dots,n_\tau\} : \frac{\rho_\ell}{\ell} + \sqrt{\frac{2\ln(8T/\ell)}{\ell}} < y\Big] \le C\,\frac{n_\tau}{T} \quad\text{and}\quad \le C\,\frac{\ln(T\varepsilon_\tau^2)}{T\varepsilon_\tau^2}.$$
--
--   In the proof of Lemma 10 the $X_\ell$ are the revenues collected when $\mathcal L_{y_\tau}$ is explored, with mean $F(y_\tau) \ge y_\tau$ when $y_\tau < \theta^*$; the event is that the policy wrongly moves $b$ below $\theta^*$, i.e. $\mathcal E_3(\tau+1)$.
--
--   **Formalization Note** This is the i.i.d.-sample form of the display's right-hand chain; identifying $\Pr[\mathcal E_3(\tau+1)]$ with it is part of the proof of Lemma 10. The sample is $n_\tau$ independent copies of a draw from a probability measure $D$, observed through a measurable $X$, $\mu = \int X\,dD$. $\lesssim$ is a universal constant chosen before every other quantity. $T \ge 25$ and "epoch $\tau$ can start" make $\ln(T\varepsilon_\tau^2) > 0$. Inner-iteration counts are $\max(1, n_\tau)$.
-- source:
--   Chen, Wang & Zhou, An Optimal Policy for Dynamic Assortment Planning Under Uncapacitated Multinomial Logit Models, arXiv:1805.04785v2, Supplement p. 7 (PDF 26), proof of Lemma 10, Eq. (S33)

import Mathlib
import Definitions.Def_UnderstandingML_Framework
import Definitions.Def_MNLTrisection_Adaptive_Model

namespace MNLTrisection.Adaptive

open MeasureTheory UnderstandingML

/-- **Eq. (S33)** (Supplement p. 7, proof of Lemma 10), in its i.i.d.-sample form. Let
`X₁, X₂, …` be i.i.d. in `[0, 1]` with mean `μ ≥ y` and `ρ_ℓ = X₁ + ⋯ + X_ℓ`. For a universal
`C`, every `T ≥ 25` and every epoch `τ` that can start,
`Pr[∃ ℓ ≤ n_τ, ρ_ℓ/ℓ + √(2 ln(8T/ℓ)/ℓ) < y] ≤ C n_τ/T` and `≤ C ln(Tε_τ²)/(Tε_τ²)`. -/
theorem eq_S33 :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (D : Measure Ω) [IsProbabilityMeasure D]
      (X : Ω → ℝ), Measurable X → (∀ᵐ ω ∂D, X ω ∈ Set.Icc (0 : ℝ) 1) →
      ∀ (y : ℝ), y ≤ ∫ x, X x ∂D →
      ∀ T τ : ℕ, 25 ≤ T → ∑ τ' ∈ Finset.range τ, nEpoch T τ' < T →
      iidLaw D (nEpoch T τ) {ω | ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ nEpoch T τ ∧
          (∑ i ∈ Finset.univ.filter (fun i : Fin (nEpoch T τ) => (i : ℕ) < ℓ), X (ω i)) / ℓ +
            radius T ℓ < y} ≤
        ENNReal.ofReal (C * (nEpoch T τ : ℝ) / T) ∧
      iidLaw D (nEpoch T τ) {ω | ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ nEpoch T τ ∧
          (∑ i ∈ Finset.univ.filter (fun i : Fin (nEpoch T τ) => (i : ℕ) < ℓ), X (ω i)) / ℓ +
            radius T ℓ < y} ≤
        ENNReal.ofReal (C * Real.log (T * eps τ ^ 2) / (T * eps τ ^ 2)) := by sorry

end MNLTrisection.Adaptive
