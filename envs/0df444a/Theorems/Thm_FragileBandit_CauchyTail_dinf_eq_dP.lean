-- Prove2me | Theorems.Thm_FragileBandit_CauchyTail_dinf_eq_dP
-- name    : FragileBandit.CauchyTail.dinf_eq_dP
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:50.404041+00:00
-- url     : https://prove2.me/theorems/fd8ac5ce-5ab5-432f-ac09-c37368710921
-- title:
--   §5.1, p. 25 (corrected: some mean of I_P exceeds µ′) — D_inf(P^µ, µ′, M_P) = d_P(µ, µ′) for µ < µ′
-- statement:
--   **$D_{\inf}$ in an exponential family.** Let $P$ be a base distribution with $0$ in the interior of $\Theta_P$, with model $\mathcal M_P = \{P^z : z\in\mathcal I_P\}$ and divergence $d_P$. Let $\mu < \mu'$ be points of $\mathcal I_P$ such that some $z \in \mathcal I_P$ exceeds $\mu'$. Then
--
--   $$D_{\inf}(P^\mu,\mu',\mathcal M_P) = \inf\{D(P^\mu\,\|\,Q') : Q'\in\mathcal M_P,\ \mu(Q') > \mu'\} = d_P(\mu,\mu').$$
--
--   This identity lets Theorem 4, stated for general models, be applied to the exponential family: with $f = \log$ its bound $1/D_{\inf}$ becomes the Lai–Robbins constant $1/d_P$ of Definition 2, which is how the paper derives the weak law of large numbers used in the proof of Theorem 1.
--
--   Differences from the source:
--   - correction: D_inf(P^µ, µ′, M_P) = d_P(µ, µ′) for µ < µ′ → adds the hypothesis ∃ z ∈ I_P with µ′ < z; reason: false when µ′ = max I_P: P(dx) ∝ e^{−x}(1+x)^{−3} on [0, ∞) has Θ_P = (−∞, 1], I_P = (0, 1]; for µ ≈ 0.354 (θ = 0) and µ′ = 1, d_P(µ, 1) ≈ 0.163 is finite while no law of M_P has mean above 1, so D_inf = inf ∅ = +∞; where the paper uses the identity (µ′ = µ₂ < µ₁ ∈ I_P) the hypothesis holds
--   - encoding: µ, µ′ the arguments of d_P → hypotheses µ ∈ I_P and µ′ ∈ I_P; reason: d_P(µ, µ′) and P^µ are defined only for means in I_P (p. 8)
--   - encoding: Θ_P = {θ : Λ_P(θ) < ∞}; P^z = exp(θ_P(z)x − Λ_P(θ_P(z))) P(dx); I_P the means of these laws; d_P the KL divergence (3) → natParamSet P = {θ : x ↦ e^{θx} is P-integrable}; tilt = Measure.tilted; meanSet P requires a finite mean; θ_P(z) a choice of θ with mean z; dP = klDiv in ℝ≥0∞; reason: same sets and laws (Λ_P(θ) < ∞ iff e^{θx} is integrable; θ_P(z) is unique unless P is a point mass, where every tilt is P); avoids the junk value 0 of Mathlib's cgf at non-integrable θ
-- source:
--   Fan, Glynn, The Fragility of Optimized Bandit Algorithms, arXiv:2109.13595v8, p. 25, §5.1, sentence after (29)

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Setting

namespace FragileBandit.CauchyTail

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm
open scoped ENNReal Topology

/-- The `D_inf` identity of §5.1 (p. 25, after (29)), corrected: for the exponential family `M_P` and
`µ < µ'` in `I_P` such that some mean in `I_P` exceeds `µ'`,
`D_inf(P^µ, µ', M_P) = d_P(µ, µ')`. -/
theorem dinf_eq_dP (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : (0 : ℝ) ∈ interior (natParamSet P)) (μ μ' : ℝ)
    (hμ : μ ∈ meanSet P) (hμ' : μ' ∈ meanSet P) (hlt : μ < μ')
    (habove : ∃ z ∈ meanSet P, μ' < z) :
    banditDInf (model P) (expFam P μ) μ' = dP P μ μ' := by sorry

end FragileBandit.CauchyTail
