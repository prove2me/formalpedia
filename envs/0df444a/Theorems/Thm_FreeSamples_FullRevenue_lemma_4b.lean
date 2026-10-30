-- Prove2me | Theorems.Thm_FreeSamples_FullRevenue_lemma_4b
-- name    : FreeSamples.FullRevenue.lemma_4b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T13:57:50.515988+00:00
-- url     : https://prove2.me/theorems/db43a93b-3071-42af-8f54-cf992def88c1
-- title:
--   Lemma 4(b) (corrected: noise-variance denominator) — all-time conditional drift
-- statement:
--   Let $u$ have the source's well-defined finite attained maxima and Assumption 1, without growth or C² pins. In the Seller Gaussian model, let $m_t,v_t$ be the Buyer posterior, $w_t$ the Seller posterior variance, $g_t=\widetilde m_t-m_t$, and $n>0$ the data noise variance. For every deterministic $t\ge0$, the actual conditional Gaussian transition $K_h$ gives a coherent version
--   $$F_t(h)=\int BR(z,v_{t+h})\,K_h(dz)=\mathbb E^S[BR(m_{t+h},v_{t+h})\mid\mathcal F_t]$$
--   for each $h\ge0$, almost surely. These random Bayes risks are integrable, as a conclusion of the model. For each $t$, almost surely,
--   $$F_t'(0+)=\left(\frac12BR_{mm}(m_t,v_t)-BR_v(m_t,v_t)+\frac{g_t}{v_t}BR_m(m_t,v_t)\right)\frac{v_t^2}{n}.$$
--   Here $BR_v$ differentiates the variance, not its square root. The identity is a right conditional drift at every time and supplies the drift used in Theorem 1(a).
--
--   The printed denominator $v_0=\sigma_0^2$ is false: for $u(a,x)=-(a-x)^2$, $\theta_0=\mu_b=\sigma_b^2=0$, $v_0=1$, $n=4$, one has $BR(m,v)=v$ and $v_h=4/(h+4)$. The actual initial drift is $-1/4$ while the printed coefficient gives $-1$. All source maxima and expectations are finite and $U,BR$ are smooth. Replacing only the denominator by $n$ gives the actual value and leaves condition (4) unchanged in sign.
--
--   Differences from the source:
--   - correction: the positive prefactor σ_t⁴/σ₀² → σ_t⁴/σ²=v_t²/n; reason: the source-admissible squared-loss example θ₀=μ_b=σ_b²=0,v₀=1,n=4 has actual drift −1/4 and printed drift −1; only the denominator is corrected
--   - reading: the conditional dt identity at every t → the right derivative of conditional transition expectation at h=0, for every deterministic t almost surely; reason: the dt display is infinitesimal and is not an exact finite-increment equality
--   - encoding: finite attained utility maxima and finite expected clairvoyant utility → BR is the finite minimum of nonnegative expected regrets, U=E[M]−BR, and unused candidate utilities may equal −∞; reason: subtracting the integrable pointwise maximum converts the same action optimization to a nonnegative integral without requiring every unused action to be integrable
--   - encoding: conditioning on the whole observed-data filtration → the computed Gaussian transition integral, together with equality to the actual conditional expectation at each h; reason: a coherent conditional version permits differentiation without asserting an uncountable common null set or assuming the generator identity
--   - generalization: the infinitesimal conditional seller drift → also the finite-increment Gaussian transition identification and Bayes-risk integrability at every finite time; reason: the same Gaussian model supplies a coherent conditional version, with these facts proved as conclusions and no added growth or integrability hypotheses
-- source:
--   Drakopoulos & Makhdoumi, Providing Data Samples for Free, SSRN 3611003, pinned local PDF snapshot (creation metadata 2021-08-30; SHA-256 2e29ad6e37639d93e587e9999f63959d3eb52c66a1fe2ac7e78f3d33976e44c0), p.17, Lemma 4(b); p.30, proof; compare p.14, Lemma 1 and p.29, its proof

import Definitions.Def_FreeSamples_FullRevenue_Policies

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace FreeSamples.FullRevenue

/-- Lemma 4(b), p.17, corrected only in its noise-variance denominator.
The transition integral is a coherent version of full-filtration conditional
expectation, identified below for every finite increment. -/
theorem lemma_4b (p : Revenue.Params) (u : ℝ → ℝ → ℝ)
    (hu : WellDefined u) (hA : Assumption1 u)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ)
    (hM : Revenue.IsModel P (p.θ₀ + p.μb) p.σssq θ B) (t : ℝ≥0) :
    (∀ h : ℝ≥0,
      Integrable (fun ω => BR u (posteriorMean p θ B (t + h) ω) (p.buyerVar (t + h))) P ∧
      P[(fun ω => BR u (posteriorMean p θ B (t + h) ω) (p.buyerVar (t + h))) |
        Revenue.dataFiltration p.σsq θ B hM.meas_θ hM.meas_B t] =ᵐ[P]
        fun ω => ∫ z, BR u z (p.buyerVar (t + h))
          ∂(transitionLaw p.σsq (posteriorMean p θ B t ω) (p.buyerVar t)
            (p.sellerVar t) (p.gMis t (Revenue.Y p.σsq θ B t ω)) h)) ∧
    ∀ᵐ ω ∂P,
      HasDerivWithinAt
        (fun h : ℝ => ∫ z, BR u z (p.buyerVar ((t : ℝ) + h))
          ∂(transitionLaw p.σsq (posteriorMean p θ B t ω) (p.buyerVar t)
            (p.sellerVar t) (p.gMis t (Revenue.Y p.σsq θ B t ω)) h))
        (Revenue.drift (BR u) (posteriorMean p θ B t ω) (p.buyerVar t)
          (p.gMis t (Revenue.Y p.σsq θ B t ω)) * (p.buyerVar t) ^ 2 / p.σsq)
        (Set.Ici 0) 0 := by sorry

end FreeSamples.FullRevenue
