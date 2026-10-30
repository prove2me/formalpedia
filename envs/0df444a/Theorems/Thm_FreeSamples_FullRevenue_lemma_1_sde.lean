-- Prove2me | Theorems.Thm_FreeSamples_FullRevenue_lemma_1_sde
-- name    : FreeSamples.FullRevenue.lemma_1_sde
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T13:54:56.317727+00:00
-- url     : https://prove2.me/theorems/ec53d279-aaae-4fac-a146-be36678bedc4
-- title:
--   Lemma 1 (SDE) — physical posterior dynamics on every finite interval
-- statement:
--   Let the Buyer prior be $N(\theta_0,v_0)$, the Seller prior be $N(\theta_0+\mu_b,v_0+\sigma_b^2)$, and let $Y_t=\Theta t+\sqrt nB_t$, with $v_0,n>0$, $\sigma_b^2\ge0$, and $B$ a standard Brownian motion independent of $\Theta$. The computed Buyer posterior has mean $m_t$ and variance $v_t=v_0n/(v_0t+n)$. Under either perspective, on every finite interval $[0,t]$, almost surely,
--   $$m_t=\theta_0+\int_0^t(\Theta-m_s)\frac{v_s}{n}\,ds+\int_0^t\frac{v_s}{\sqrt n}\,dB_s.$$
--   The ordinary drift and integration-by-parts terms are interval integrable. This is the physical posterior SDE, including the latent state and the physical Brownian noise, rather than only its expected drift.
--
--   Differences from the source:
--   - reading: the physical stochastic differential equation → its integral identity on every finite interval, for each time almost surely; reason: the integral identity gives the literal meaning of the source differential notation
--   - encoding: the deterministic Brownian integral of v_s/σ → its integration-by-parts representation for the smooth deterministic coefficient v_s/√n; reason: for this coefficient the representation agrees with the Wiener/Itô integral and assumes no dynamics or expectation identity
--   - encoding: real continuous sample amounts and Gaussian variances → nonnegative-real time indices, real positive variances and √n as noise standard deviation; reason: these types preserve all source instances and prevent zero-denominator or variance/standard-deviation confusion
-- source:
--   Drakopoulos & Makhdoumi, Providing Data Samples for Free, SSRN 3611003, pinned local PDF snapshot (creation metadata 2021-08-30; SHA-256 2e29ad6e37639d93e587e9999f63959d3eb52c66a1fe2ac7e78f3d33976e44c0), p.14, Lemma 1, opening SDE; p.29, proof, Eq.(14)

import Definitions.Def_FreeSamples_FullRevenue_Learning
import Definitions.Def_FreeSamples_FullRevenue_DeterministicIntegral

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace FreeSamples.FullRevenue

/-- Lemma 1 opening SDE, p.14: the physical Brownian integral identity,
under either perspective and on every finite interval [0,t]. -/
theorem lemma_1_sde (p : Revenue.Params) (i : Perspective)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ)
    (hM : Revenue.IsModel P (priorMean p i) (priorVariance p i) θ B) (t : ℝ≥0) :
    ∀ᵐ ω ∂P,
      IntervalIntegrable (fun s : ℝ =>
        (θ ω - posteriorMean p θ B s.toNNReal ω) * p.buyerVar s / p.σsq) volume 0 t ∧
      IntervalIntegrable (fun s : ℝ =>
        deriv (fun r : ℝ => p.buyerVar r / Real.sqrt p.σsq) s * B s.toNNReal ω)
        volume 0 t ∧
      posteriorMean p θ B t ω = p.θ₀ +
        (∫ s in (0 : ℝ)..(t : ℝ),
          (θ ω - posteriorMean p θ B s.toNNReal ω) * p.buyerVar s / p.σsq) +
        deterministicWienerIntegral (fun s : ℝ => p.buyerVar s / Real.sqrt p.σsq) B t ω := by sorry

end FreeSamples.FullRevenue
