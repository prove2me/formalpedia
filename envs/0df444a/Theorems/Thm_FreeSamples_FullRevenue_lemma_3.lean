-- Prove2me | Theorems.Thm_FreeSamples_FullRevenue_lemma_3
-- name    : FreeSamples.FullRevenue.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T13:57:07.276613+00:00
-- url     : https://prove2.me/theorems/8c7edb3a-ef40-4c8c-b7c9-3ef1cdc52393
-- title:
--   Lemma 3 — optimal full-remainder allocation and exact Bayes-risk price
-- statement:
--   Let $u(a,x)$ have the source's attained pointwise and Bayesian maxima, finite optimized expectations, and Assumption 1. Let the Buyer posterior belief be $N(m,v)$ with $m\in\mathbb R$ and $v>0$. A terminal offer releases any amount $k\in[0,\infty]$ at a nonnegative price $q$; $k=\infty$ reveals the latent state. Write $W(k;m,v)$ for the genuine expected gain in the Buyer's optimized utility, and $\operatorname{pay}(k,q;m,v)$ for $q$ if the Buyer accepts and zero otherwise. Then
--   $$0\le W(k;m,v)\le BR(m,v),\qquad W(\infty;m,v)=BR(m,v),$$
--   $$\operatorname{pay}(\infty,BR(m,v);m,v)=BR(m,v),\qquad\operatorname{pay}(k,q;m,v)\le BR(m,v).$$
--   The Bayes risk is finite and post-signal optimized utility is integrable; these are conclusions, not added hypotheses.
--
--   For every observed-data stopping time $T$, without any bound or finite-mean requirement, there is an admissible full-sale policy at that same $T$ with price $BR(m_T,v_T)$ almost surely and
--   $$R(\pi_*)=\mathbb E^S[BR(m_T,v_T)\mathbf1\{T<\infty\}],\qquad R(\pi)\le R(\pi_*)$$
--   for every admissible terminal offer at $T$. At $T=\infty$, the revenue is zero. Thus the optimal terminal allocation and price follow from the Buyer's utility maximization, including acceptance at indifference, and also give the one-round revenue ceiling at $T=0$.
--
--   Differences from the source:
--   - encoding: finite attained utility maxima and finite expected clairvoyant utility → BR is the finite minimum of nonnegative expected regrets, U=E[M]−BR, and unused candidate utilities may equal −∞; reason: subtracting the integrable pointwise maximum converts the same action optimization to a nonnegative integral without requiring every unused action to be integrable
--   - reading: stopping amount measurable with respect to the players’ information → a stopping time of the natural whole-signal filtration, with allocation and price measurable at that stopping time; reason: the source repeatedly calls T a stopping amount/time, including its proof on p.30; terminal measurability alone would allow foresight
--   - encoding: finite terminal sales and arbitrary source-admissible free-sample policies → all nonanticipating continuous-time policies, with ∞ denoting never selling and zero payment, and nonnegative extended expected revenue; reason: no deterministic bound, finite-mean assumption or integrability restriction is imposed; adding the zero-revenue never-sell limit does not change the optimum
--   - encoding: a subset of the remaining indistinguishable data, or complete revelation → finite additional sample amount k with its Gaussian signal law, or k=∞ revealing Θ; reason: §2.2 restricts offers to numbers of new samples, and the p.30 proof represents each partial offer by a Gaussian signal
--   - encoding: price BR at the stopping state → an admissible full-sale policy with that price almost surely, allowing observable versions on null paths; reason: Brownian paths are continuous almost surely and source prices and revenues are unchanged by null-set version choices; exact measurability is retained for the actual offer
-- source:
--   Drakopoulos & Makhdoumi, Providing Data Samples for Free, SSRN 3611003, pinned local PDF snapshot (creation metadata 2021-08-30; SHA-256 2e29ad6e37639d93e587e9999f63959d3eb52c66a1fe2ac7e78f3d33976e44c0), p.16, Lemma 3 and policy definition; p.30, proof

import Definitions.Def_FreeSamples_FullRevenue_Policies

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace FreeSamples.FullRevenue

/-- Lemma 3, p.16: the exact terminal offer is optimal for all stopping
amounts, all source utilities and all terminal allocations/prices. -/
theorem lemma_3 (p : Revenue.Params) (u : ℝ → ℝ → ℝ)
    (hu : WellDefined u) (hA : Assumption1 u) :
    (∀ m v : ℝ, 0 < v →
      bayesRisk u m v < ⊤ ∧
      (∀ k : WithTop ℝ≥0,
        0 ≤ willingnessToPay u p.σsq m v k ∧
        willingnessToPay u p.σsq m v k ≤ BR u m v) ∧
      willingnessToPay u p.σsq m v ⊤ = BR u m v ∧
      payment u p.σsq m v ⊤ (BR u m v).toNNReal = BR u m v ∧
      (∀ (k : WithTop ℝ≥0) (q : ℝ≥0), payment u p.σsq m v k q ≤ BR u m v) ∧
      ∀ k : ℝ≥0, Integrable
        (fun y => U u (Revenue.postMean p.σsq m v k y) (Revenue.postVar p.σsq v k))
        (Revenue.N (m * k) (v * k ^ 2 + p.σsq * k))) ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ)
      (hM : Revenue.IsModel P (p.θ₀ + p.μb) p.σssq θ B)
      (T : Ω → WithTop ℝ≥0),
      IsStoppingTime (Revenue.dataFiltration p.σsq θ B hM.meas_θ hM.meas_B) T →
      ∃ πstar : PolicyData Ω,
        IsAdmissible (Revenue.dataFiltration p.σsq θ B hM.meas_θ hM.meas_B) πstar ∧
        πstar.stop = T ∧ (∀ ω, πstar.allocation ω = ⊤) ∧
        πstar.price =ᵐ[P] (fullSale p u θ B T).price ∧
        expectedRevenue p u P θ B πstar = ∫⁻ ω, stoppingReward p u θ B T ω ∂P ∧
        ∀ π : PolicyData Ω,
          IsAdmissible (Revenue.dataFiltration p.σsq θ B hM.meas_θ hM.meas_B) π →
          π.stop = T →
          expectedRevenue p u P θ B π ≤ expectedRevenue p u P θ B πstar := by sorry

end FreeSamples.FullRevenue
