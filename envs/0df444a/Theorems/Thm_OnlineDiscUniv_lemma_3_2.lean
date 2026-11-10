-- Prove2me | Theorems.Thm_OnlineDiscUniv_lemma_3_2
-- name    : OnlineDiscUniv.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:17:03.038967+00:00
-- url     : https://prove2.me/theorems/abcd84a8-f496-4dfb-8730-1f25df401b6c
-- title:
--   Lemma 3.2 — $\mathbb P(\varepsilon=\sigma)=(1+\sigma t)/2$ and the conditional density of $\zeta$ given $\varepsilon=\sigma$
-- statement:
--   Let $\zeta\sim\nu^{\otimes M}$ and let $\varepsilon$ be chosen by the rule (3.16) with $\|v\|_2=1$ and $0\le\rho\le c_*-\delta$. With $t=\mathbb E\psi_\rho(\langle v,\zeta\rangle)$, for $\sigma\in\{-1,1\}$,
--   $$
--   \mathbb P(\varepsilon=\sigma)=\frac{1+\sigma t}{2},\qquad\frac{d\,\mathrm{Law}(\zeta\mid\varepsilon=\sigma)}{d\nu^{\otimes M}}(x)=\frac{1+\sigma\psi_\rho(\langle v,x\rangle)}{1+\sigma t}.\qquad(3.18)
--   $$
--   In particular the conditional density lies between
--   $$
--   \frac{1-a_\delta}{1+a_\delta}\quad\text{and}\quad\frac{1+a_\delta}{1-a_\delta}.\qquad(3.19)
--   $$
--
--   The bounded density lets the chosen sign be coupled to a fair sign and an independent vector even when $\nu$ is not symmetric (Lemma 3.3).
--
--   Differences from the source:
--   - generalization: L = L_δ < ∞ chosen so that (3.4) holds → every L with c_* − δ/2 < E[G tanh(LG)]; constants may depend on (δ, L, K₃); reason: the paper's L_δ is one such L, so the statement specializes to the source's
--   - encoding: Law(ζ | ε = σ) and its density; P(ε = σ) → the image under ζ of the conditional measure cond (steerLaw) {ε = σ} equals ν^{⊗M}.withDensity of the density; P(ε = σ) = ofReal((1 + σt)/2) in ℝ≥0∞; (3.19) for the density at every x; reason: the same statements about the law of (ε, ζ) under (3.16), modelled as the image of ν^{⊗M} ⊗ Unif[−1,1]
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), Lemma 3.2, (3.16)–(3.19), p.8 (PDF p.9)

import Mathlib
import Definitions.Def_OnlineDiscUniv_steerLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace OnlineDiscUniv

/-- **Lemma 3.2** (Jo–Lee, arXiv:2610.00103, artifact sha256 cb190f12…, printed p.8, PDF p.9).
Under the sign rule (3.16), with `t = Eψ_ρ(⟨v, ζ⟩)`, for `σ ∈ {−1, 1}`,
`P(ε = σ) = (1 + σt)/2` and `d Law(ζ | ε = σ)/dν^{⊗M}(x) = (1 + σψ_ρ(⟨v, x⟩))/(1 + σt)` (3.18). In
particular the conditional density lies between `(1 − a_δ)/(1 + a_δ)` and `(1 + a_δ)/(1 − a_δ)`
(3.19).

**Formalization Note** The randomness is modelled explicitly: `ζ ∼ ν^{⊗M}` and
`U' ∼ Unif[−1,1]` independent, and `ε` the function (3.16) of `(ζ, U')` (`steerLaw`). The
standing assumptions (3.3)–(3.5) and (3.15) of the rule are kept: `0 < δ < c_*`, `L` with (3.4),
`0 ≤ ρ ≤ c_* − δ`, `‖v‖_2 = 1`; `ν` is any probability law on `ℝ`. The conditional law is
`ProbabilityTheory.cond`, and the density claim is an equality of measures with
`ν^{⊗M}.withDensity`; the bounds (3.19) are stated for the density at every `x`. -/
theorem lemma_3_2 (δ L : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < cStar) (hL : cStar - δ / 2 < mL L)
    (M : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν] (v : Fin M → ℝ) (hv : ∑ j, v j ^ 2 = 1)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ cStar - δ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    let t : ℝ := ∫ x, psi L ρ (∑ j, v j * x j) ∂(Measure.pi fun _ : Fin M => ν)
    steerLaw ν L ρ v {p | p.1 = σ} = ENNReal.ofReal ((1 + σ * t) / 2) ∧
    (ProbabilityTheory.cond (steerLaw ν L ρ v) {p | p.1 = σ}).map Prod.snd =
      (Measure.pi fun _ : Fin M => ν).withDensity
        (fun x => ENNReal.ofReal ((1 + σ * psi L ρ (∑ j, v j * x j)) / (1 + σ * t))) ∧
    ∀ x : Fin M → ℝ,
      (1 - aDelta δ) / (1 + aDelta δ) ≤ (1 + σ * psi L ρ (∑ j, v j * x j)) / (1 + σ * t) ∧
      (1 + σ * psi L ρ (∑ j, v j * x j)) / (1 + σ * t) ≤ (1 + aDelta δ) / (1 - aDelta δ) := by sorry

end OnlineDiscUniv
