-- Prove2me | Theorems.Thm_FreeSamples_FullRevenue_theorem_1a
-- name    : FreeSamples.FullRevenue.theorem_1a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T13:58:38.014879+00:00
-- url     : https://prove2.me/theorems/92068da5-efe7-48fe-9eac-d66746c3ec31
-- title:
--   Theorem 1(a) — positive initial Bayes-risk drift strictly improves optimal revenue
-- statement:
--   Let $u(a,x)$ be any source-admissible downstream utility on real actions and real states, with finite attained Bayesian and pointwise maxima and with $U$ and $BR$ continuous and twice differentiable on positive variance. The Buyer prior is $N(\theta_0,v_0)$, and the Seller's correct prior is $N(\theta_0+\mu_b,v_0+\sigma_b^2)$, where $\theta_0,\mu_b\in\mathbb R$, $v_0,n>0$ and $\sigma_b^2\ge0$. Data are $Y_t=\Theta t+\sqrt nB_t$ with independent Brownian noise, observed through the whole signal filtration. Let $V_{\rm free}$ be the supremum of the actual Seller expected accepted payments over every admissible free-sample stopping policy and terminal partial/full offer.
--
--   If
--   $$\frac12BR_{mm}(\theta_0,v_0)-BR_v(\theta_0,v_0)+\frac{\mu_b}{v_0}BR_m(\theta_0,v_0)>0,$$
--   then the initial Bayes risk is finite and
--   $$BR(\theta_0,v_0)<V_{\rm free},\qquad R(\pi_0)\le BR(\theta_0,v_0)<V_{\rm free}\quad\text{for every one-round offer }\pi_0.$$
--   Moreover, an admissible free-sample policy $\pi$ satisfies $BR(\theta_0,v_0)<R(\pi)$. Every expectation is under the Seller's correct prior. No bound on stopping amounts, finite-mean requirement, growth assumption, C² strengthening or existence of a maximizing policy is assumed.
--
--   This is the full optimal-value and static-policy comparison in Theorem 1(a), including all signs of the prior misspecification and zero bias variance. Any free-sample policy attaining the optimal value therefore strictly outperforms every one-round offer.
--
--   Differences from the source:
--   - reading: revenue of the optimal free-sample policy → the supremum of attainable revenues, the ceiling for every one-round offer and a strictly improving admissible witness; reason: the source proof exhibits an improving policy, not existence of a maximizer; any actually attaining optimizer has the printed strict comparison
--   - encoding: finite attained utility maxima and finite expected clairvoyant utility → BR is the finite minimum of nonnegative expected regrets, U=E[M]−BR, and unused candidate utilities may equal −∞; reason: subtracting the integrable pointwise maximum converts the same action optimization to a nonnegative integral without requiring every unused action to be integrable
--   - reading: stopping amount measurable with respect to the players’ information → a stopping time of the natural whole-signal filtration, with allocation and price measurable at that stopping time; reason: the source repeatedly calls T a stopping amount/time, including its proof on p.30; terminal measurability alone would allow foresight
--   - encoding: finite terminal sales and arbitrary source-admissible free-sample policies → all nonanticipating continuous-time policies, with ∞ denoting never selling and zero payment, and nonnegative extended expected revenue; reason: no deterministic bound, finite-mean assumption or integrability restriction is imposed; adding the zero-revenue never-sell limit does not change the optimum
-- source:
--   Drakopoulos & Makhdoumi, Providing Data Samples for Free, SSRN 3611003, pinned local PDF snapshot (creation metadata 2021-08-30; SHA-256 2e29ad6e37639d93e587e9999f63959d3eb52c66a1fe2ac7e78f3d33976e44c0), p.17, Theorem 1(a), Eq.(4); p.18, Seller expectation convention; pp.30–31, proof

import Definitions.Def_FreeSamples_FullRevenue_Policies

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace FreeSamples.FullRevenue

/-- Theorem 1(a), Eq.(4), p.17, with Seller expectation (p.18).
The optimal value and the entire one-round comparison are explicit. -/
theorem theorem_1a (p : Revenue.Params) (u : ℝ → ℝ → ℝ)
    (hu : WellDefined u) (hA : Assumption1 u)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ)
    (hM : Revenue.IsModel P (p.θ₀ + p.μb) p.σssq θ B)
    (hpositive : 0 < Revenue.drift (BR u) p.θ₀ p.σ₀sq p.μb) :
    bayesRisk u p.θ₀ p.σ₀sq < ⊤ ∧
    ENNReal.ofReal (BR u p.θ₀ p.σ₀sq) <
      optimalRevenue p u P θ B (Revenue.dataFiltration p.σsq θ B hM.meas_θ hM.meas_B) ∧
    (∀ π : PolicyData Ω,
      IsOneRound P (Revenue.dataFiltration p.σsq θ B hM.meas_θ hM.meas_B) π →
      expectedRevenue p u P θ B π ≤ ENNReal.ofReal (BR u p.θ₀ p.σ₀sq) ∧
      expectedRevenue p u P θ B π <
        optimalRevenue p u P θ B (Revenue.dataFiltration p.σsq θ B hM.meas_θ hM.meas_B)) ∧
    ∃ π : PolicyData Ω,
      IsAdmissible (Revenue.dataFiltration p.σsq θ B hM.meas_θ hM.meas_B) π ∧
      ENNReal.ofReal (BR u p.θ₀ p.σ₀sq) < expectedRevenue p u P θ B π := by sorry

end FreeSamples.FullRevenue
