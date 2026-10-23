-- Prove2me | Theorems.Thm_MNLTrisection_Adaptive_eq_S32
-- name    : MNLTrisection.Adaptive.eq_S32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:50.408226+00:00
-- url     : https://prove2.me/theorems/2ae80104-f5aa-4354-a7b1-0b913cbab950
-- title:
--   Eq. (S32), Supplement p. 7 (PDF 26), repaired — missing the detection y > F(y) for n_τ explorations has probability ≤ exp{−n_τΔ²/2}
-- statement:
--   Let $X_1, X_2, \dots$ be i.i.d. with values in $[0,1]$ and mean $\mu$, let $\rho_\ell = X_1 + \dots + X_\ell$, and let $\Delta = y - \mu$. With $\varepsilon_\tau = \tfrac13(\tfrac23)^\tau$ and $n_\tau = 8\lceil \varepsilon_\tau^{-2}\ln(8T\varepsilon_\tau^2)\rceil$, for every $T \ge 25$, every epoch $\tau$ with $\sum_{\tau'<\tau} n_{\tau'} < T$, and $\Delta \ge \varepsilon_\tau$,
--   $$\Pr\Big[\forall \ell \in \{1,\dots,n_\tau\} : \frac{\rho_\ell}{\ell} + \sqrt{\frac{2\ln(8T/\ell)}{\ell}} \ge y\Big] \le \exp\{-n_\tau\Delta^2/2\}.$$
--
--   In the proof of Lemma 10 the $X_\ell$ are the revenues collected when $\mathcal L_{y_\tau}$ is explored, with mean $F(y_\tau) \le y_\tau - \varepsilon_\tau$ when $\theta^* < x_\tau$; the event is that the policy never detects $F(y_\tau) < y_\tau$ and moves $a$ above $\theta^*$, i.e. $\mathcal E_1(\tau+1)$.
--
--   **Formalization Note** The printed bound $\exp\{-n_\tau\Delta_\tau^2\}$ is false (one item, $r_1 = 1$, $v_1 = 0.49$, $T = 10^6$, $\tau = 0$: the probability is $4.2\cdot10^{-40} > \exp(-n_0\Delta_0^2) = 6.9\cdot10^{-50}$); the justification printed below the display gives $\exp\{-n_\tau\Delta_\tau^2/2\}$, which is stated. The event uses "$\ge y$" (no detection means $u \ge y$), a superset of the page's "$> y$". The page's second line "$\sqrt{2\ln(8T/\ell)/n_\tau}$" is a typo for $\ell = n_\tau$. The sample is $n_\tau$ independent copies of a draw from $D$ observed through a measurable $X$, $\mu = \int X\,dD$. Inner-iteration counts are $\max(1, n_\tau)$.
-- source:
--   Chen, Wang & Zhou, An Optimal Policy for Dynamic Assortment Planning Under Uncapacitated Multinomial Logit Models, arXiv:1805.04785v2, Supplement p. 7 (PDF 26), proof of Lemma 10, Eq. (S32)

import Mathlib
import Definitions.Def_UnderstandingML_Framework
import Definitions.Def_MNLTrisection_Adaptive_Model

namespace MNLTrisection.Adaptive

open MeasureTheory UnderstandingML

/-- **Eq. (S32)** (Supplement p. 7, proof of Lemma 10), in its i.i.d.-sample form and with the
exponent `−n_τ Δ²/2` that its printed justification gives (the printed `−n_τ Δ²` is false). Let
`X₁, X₂, …` be i.i.d. in `[0, 1]` with mean `μ`, `ρ_ℓ = X₁ + ⋯ + X_ℓ`, and `Δ = y − μ ≥ ε_τ`.
For every `T ≥ 25` and every epoch `τ` that can start,
`Pr[∀ ℓ ≤ n_τ, ρ_ℓ/ℓ + √(2 ln(8T/ℓ)/ℓ) ≥ y] ≤ exp{−n_τ Δ²/2}`. -/
theorem eq_S32 {Ω : Type*} [MeasurableSpace Ω] (D : Measure Ω) [IsProbabilityMeasure D]
    (X : Ω → ℝ) (hX : Measurable X) (hX01 : ∀ᵐ ω ∂D, X ω ∈ Set.Icc (0 : ℝ) 1)
    (y : ℝ) (T τ : ℕ) (hT : 25 ≤ T) (hτ : ∑ τ' ∈ Finset.range τ, nEpoch T τ' < T)
    (hΔ : eps τ ≤ y - ∫ x, X x ∂D) :
    iidLaw D (nEpoch T τ) {ω | ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ nEpoch T τ →
        y ≤ (∑ i ∈ Finset.univ.filter (fun i : Fin (nEpoch T τ) => (i : ℕ) < ℓ), X (ω i)) / ℓ +
          radius T ℓ} ≤
      ENNReal.ofReal (Real.exp (-((nEpoch T τ : ℝ) * (y - ∫ x, X x ∂D) ^ 2 / 2))) := by sorry

end MNLTrisection.Adaptive
