-- Prove2me | Theorems.Thm_FreeSamples_FullRevenue_lemma_1_iii
-- name    : FreeSamples.FullRevenue.lemma_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T13:56:16.614776+00:00
-- url     : https://prove2.me/theorems/3b609f5f-f807-4956-b397-a4d8aa0d687d
-- title:
--   Lemma 1(iii) — exact conditional squared increments and explicit remainder
-- statement:
--   In the Gaussian model, fix a deterministic time $t\ge0$. Write $v=v_t$ for the Buyer posterior variance and $n>0$ for the noise variance. For the Buyer put $(w,g)=(v_t,0)$; for the Seller put $(w,g)=(w_t,g_t)$, with Seller posterior variance $w_t$ and mean difference $g_t$. For every $h\ge0$, the squared increment is integrable and its full-filtration conditional expectation is, almost surely,
--   $$Q(h):=\mathbb E^i[(m_{t+h}-m_t)^2\mid\mathcal F_t]=\frac{v^2\{nh+(w+g^2)h^2\}}{(vh+n)^2}.$$
--   For the coherent rational version, every $0<h\le1$ satisfies
--   $$\left|Q(h)-\frac{v^2}{n}h\right|\le C(v,w,g,n)h^2\le C(v,w,g,n)h^{3/2},$$
--   $$C(v,w,g,n)=\frac{v^2}{n^2}\left(w+g^2+2v+\frac{v^2}{n}\right)\ge0.$$
--   The paper writes $O(h^{3/2})$; its Gaussian calculation on p.29 yields the displayed constant after a common-denominator bound. It depends only on the current state and parameters, never on $h$. The result supplies the complete all-time, both-measure quadratic-variation input to Lemma 4.
--
--   Differences from the source:
--   - reading: d(θ_t)^2 in the local second-moment calculation → the square (m_{t+h}−m_t)² of the increment; reason: p.29 explicitly expands the squared increment, rather than the differential of m_t²
--   - generalization: conditional leading term plus O(h^(3/2)) → the exact conditional second moment and an O(h²) bound, followed by the source O(h^(3/2)) bound; reason: the same Gaussian calculation proves the exact formula and h²≤h^(3/2) for 0<h≤1
--   - encoding: an implicit local O constant → C=v²/n²·(w+g²+2v+v²/n), independent of h; reason: bringing the exact Gaussian formula to a common denominator and using vh+n≥n gives this explicit coefficient
--   - encoding: both conditional moment assertions at every t → a perspective parameter, full-filtration conditional expectations and coherent rational versions; reason: the Buyer uses (w,g)=(v_t,0), the Seller uses (w_t,g_t), and no simultaneous null set over t is asserted
-- source:
--   Drakopoulos & Makhdoumi, Providing Data Samples for Free, SSRN 3611003, pinned local PDF snapshot (creation metadata 2021-08-30; SHA-256 2e29ad6e37639d93e587e9999f63959d3eb52c66a1fe2ac7e78f3d33976e44c0), p.14, Lemma 1(iii); p.29, squared-increment Gaussian calculation

import Definitions.Def_FreeSamples_FullRevenue_Learning

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace FreeSamples.FullRevenue

/-- Lemma 1(iii), p.14; the exact Gaussian moment makes the p.29
O(h^(3/2)) precise, uniformly for 0<h≤1 and at every deterministic time. -/
theorem lemma_1_iii (p : Revenue.Params) (i : Perspective)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ)
    (hM : Revenue.IsModel P (priorMean p i) (priorVariance p i) θ B) (t : ℝ≥0) :
    (∀ h : ℝ≥0,
      Integrable (fun ω => (posteriorMean p θ B (t + h) ω - posteriorMean p θ B t ω) ^ 2) P ∧
      P[(fun ω => (posteriorMean p θ B (t + h) ω - posteriorMean p θ B t ω) ^ 2) |
        Revenue.dataFiltration p.σsq θ B hM.meas_θ hM.meas_B t] =ᵐ[P]
        fun ω => secondMoment (p.buyerVar t) (currentVariance p i t)
          (currentGap p i t (Revenue.Y p.σsq θ B t ω)) p.σsq h) ∧
    ∀ᵐ ω ∂P, ∀ h ∈ Set.Ioc (0 : ℝ) 1,
      let v := p.buyerVar t
      let w := currentVariance p i t
      let g := currentGap p i t (Revenue.Y p.σsq θ B t ω)
      0 ≤ remainderConstant v w g p.σsq ∧
      |secondMoment v w g p.σsq h - v ^ 2 / p.σsq * h| ≤
          remainderConstant v w g p.σsq * h ^ 2 ∧
      remainderConstant v w g p.σsq * h ^ 2 ≤
          remainderConstant v w g p.σsq * h ^ ((3 : ℝ) / 2) := by sorry

end FreeSamples.FullRevenue
