-- Prove2me | Theorems.Thm_GaussMixHH_proposition_19
-- name    : GaussMixHH.proposition_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:34:20.854434+00:00
-- url     : https://prove2.me/theorems/3ba14818-8864-4d1a-a3ce-29fc20f96468
-- title:
--   Proposition 19, p.25 — one frequency interval $I=[c_0\lambda^2,C_0\lambda]$ on which $\mathbb E_{\mathrm{Unif}(I)}|\Phi_{\rho_1}-\Phi_{\rho_2}|^2\ge c\lambda e^{-CA}$
-- statement:
--   There are universal constants $c,C,c_0,C_0>0$ such that the following holds. Let $0<R\le1$, $0<\eta<1/4$, $k$ an odd integer whose $P_k$ satisfies Lemma 17's approximation bounds for $\eta$, $\beta=\eta/(2\cdot3^k)$, $n\in\mathbb N$, and
--
--   $$L=\log(2/\beta),\qquad B=\frac{kL}{R^2},\qquad\lambda=(B/n)^{1/3},\qquad A=B^{2/3}n^{1/3}.$$
--
--   If $n\ge CB$, then $\theta_0=c_0\lambda^2$ and $q=C_0\lambda$ satisfy $\theta_0<q\le1/2$, and for every pair of $(R/2,R)$-gapped probability distributions $\rho_1,\rho_2$ whose near masses differ by at least $\eta$,
--
--   $$\mathbb E_{\theta\sim\mathrm{Unif}([\theta_0,q])}\big[|\Phi_{\rho_1}(\theta)-\Phi_{\rho_2}(\theta)|^2\big]\ge c\lambda e^{-CA}.$$
--
--   The interval depends on $n$, $R$, $\eta$ only, so the algorithm can draw its test frequencies from it without knowing the competing distributions.
--
--   **Formalization Note** $\Phi_\rho$ is the right side of (6); the uniform average is $(q-\theta_0)^{-1}\int_{\theta_0}^q$.
--
--   Differences from the source:
--   - generalization: k and β as above (Lemma 17's k) → every odd k whose P_k satisfies Lemma 17's approximation bounds, β = η/(2·3^k); reason: the proof uses only Lemma 18 and those bounds; Lemma 17's k is one such k
--   - reading: I = [θ0, q] with E_{θ∼Unif(I)} → θ₀ < q is a conclusion, alongside q ≤ 1/2; reason: a uniform law on I presupposes |I| > 0; the proof's c0 < c′/2 gives it
--   - encoding: E_{θ∼Unif(I)} → (q − θ₀)⁻¹ ∫_{θ₀}^{q}; reason: the uniform average on an interval
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), Proposition 19, p.25 (PDF p.27); standing assumptions of §4.3, p.23

import Mathlib
import Definitions.Def_GaussMixHH_RadialTransform
import Definitions.Def_GaussMixHH_Gapped
import Definitions.Def_GaussMixHH_MajorityPoly
import Definitions.Def_GaussMixHH_GridFit

open MeasureTheory Complex

namespace GaussMixHH

/-- **Proposition 19** (A common frequency interval for detecting differences in near mass).

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), Proposition 19, p.25 (PDF p.27),
with `0 < R ≤ 1`, `0 < η < 1/4` fixed at the start of §4.3, p.23.

"With k and β as above, set L = log(2/β), B = kL/R², λ = (B/n)^{1/3}, A = B^{2/3}n^{1/3}. Suppose
n ≥ CB. There are universal constants c0, C0 > 0 such that the interval I = [θ0, q], θ0 = c0λ²,
q = C0λ ≤ 1/2 satisfies the following guarantee for every pair of (R/2, R)-gapped probability
distributions whose near masses differ by at least η:
E_{θ∼Unif(I)}[|Φ_{ρ1}(θ) − Φ_{ρ2}(θ)|²] ≥ cλe^{−CA}."

**Formalization Note.**
* Generalization: `k` is any odd natural number whose `P_k` satisfies Lemma 17's approximation
  bounds (`MajorityApprox k η`), not only Lemma 17's `k`; `β = η/(2·3^k)` as in Lemma 18.
* `c, C, c₀, C₀` are universal, chosen before `R, η, k, n`. `θ₀ < q` and `q ≤ 1/2` are
  conclusions (an empty interval would make the average meaningless).
* `E_{θ∼Unif(I)}` is `avgI θ₀ q = (q − θ₀)⁻¹ ∫_{θ₀}^{q}`. `Φ_ρ` is the analytic right side of (6),
  `PhiRad n ρ`. `λ` is written `lam`. -/
theorem proposition_19 :
    ∃ c C c₀ C₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < c₀ ∧ 0 < C₀ ∧
      ∀ (R η : ℝ), 0 < R → R ≤ 1 → 0 < η → η < 1 / 4 →
      ∀ k : ℕ, Odd k → MajorityApprox k η → ∀ n : ℕ,
        let β := η / (2 * 3 ^ k)
        let L := Real.log (2 / β)
        let B := k * L / R ^ 2
        let lam := (B / n) ^ ((1 : ℝ) / 3)
        let A := B ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((1 : ℝ) / 3)
        C * B ≤ n →
          c₀ * lam ^ 2 < C₀ * lam ∧ C₀ * lam ≤ 1 / 2 ∧
          ∀ (ρ₁ ρ₂ : Measure ℝ), IsProbabilityMeasure ρ₁ → IsProbabilityMeasure ρ₂ →
            IsGapped R ρ₁ → IsGapped R ρ₂ → η ≤ |nearMass R ρ₁ - nearMass R ρ₂| →
            c * lam * Real.exp (-(C * A)) ≤
              avgI (c₀ * lam ^ 2) (C₀ * lam) (fun θ => ‖PhiRad n ρ₁ θ - PhiRad n ρ₂ θ‖ ^ 2) := by sorry

end GaussMixHH
