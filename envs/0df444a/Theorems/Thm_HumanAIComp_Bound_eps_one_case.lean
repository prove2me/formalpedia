-- Prove2me | Theorems.Thm_HumanAIComp_Bound_eps_one_case
-- name    : HumanAIComp.Bound.eps_one_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:38.286142+00:00
-- url     : https://prove2.me/theorems/2f12f6d3-e5cd-4af5-bc41-a384c6417360
-- title:
--   Proof of Theorem 1, Appendix K, p. 46 — the case ε = 1: b − a > δ a.s. under every coupling (corrected: no threshold t* need exist; only "b − a > δ a.s. under every coupling" is kept)
-- statement:
--   Let $\mu_a,\mu_b$ be probability measures on $\mathbb R$ with cumulative distribution functions $F_a,F_b$, let $\delta\ge0$, and suppose
--   $$
--   \varepsilon\;=\;\sup_{t\in\mathbb R}\bigl(F_a(t)-F_b(t+\delta)\bigr)\;=\;1 .
--   $$
--   Then for every coupling $\pi$ of $\mu_a$ and $\mu_b$ (a probability measure on $\mathbb R^2$ whose first marginal is $\mu_a$ and whose second marginal is $\mu_b$), $b-a>\delta$ holds $\pi$-almost surely.
--
--   This is the degenerate case of the tightness half of Theorem 1: when $\varepsilon=1$ every coupling attains the bound.
--
--   **Correction.** The printed proof derives this from the claim that $a\le t^*$ a.s. and $b>t^*+\delta$ a.s. for some threshold $t^*$. That claim is false when the supremum is not attained: for $\delta=1/2$, $a\sim\mathrm{Uniform}(-1,0)$ and $b\equiv 1/2$, one has $F_a(t)-F_b(t+1/2)=F_a(t)\to1$ as $t\uparrow0$ and $=0$ for $t\ge0$, so $\varepsilon=1$, but $a\le t^*$ a.s. forces $t^*\ge0$ while $b>t^*+1/2$ a.s. forces $t^*<0$. The conclusion is still true, and is what is stated here.
--
--   Differences from the source:
--   - correction: if ε = 1 then a ≤ t* a.s. and b > t* + δ a.s. for some t*, so b − a > δ a.s. under every coupling → if ε = 1 then b − a > δ π-a.s. for every π ∈ transferencePlans μa μb (no threshold t* is asserted); reason: counterexample δ = 1/2, μa = Uniform(−1, 0), μb = Dirac(1/2): ε = 1 is approached as t ↑ 0 but not attained, and no t* exists (a ≤ t* a.s. needs t* ≥ 0, b > t* + 1/2 a.s. needs t* < 0); the conclusion holds (it follows from the lower bound); checked in missions/_checks/baek2026_tightness_check.py
--   - encoding: the CDFs F_a, F_b of a and b → two probability measures μa, μb on ℝ with F_a = cdf μa, F_b = cdf μb; reason: every probability law on ℝ is the law of a real random variable and conversely; same instances
--   - encoding: ε = sup_{t∈ℝ} (F_a(t) − F_b(t + δ)) → makarovBound δ μa μb = ⨆ t : ℝ, (cdf μa t − cdf μb (t + δ)); reason: the family lies in [−1, 1], so the real iSup is the true supremum; same value
--   - encoding: a joint distribution (coupling) of (a, b) with the given marginals → π ∈ MongeKantorovichYao.transferencePlans μa μb (a probability measure on ℝ × ℝ with π.map Prod.fst = μa, π.map Prod.snd = μb), a = p.1, b = p.2; reason: this is exactly the set of joint laws with those marginals; same instances
-- source:
--   Baek, Fu, Ma, Peng, AI Agents for Inventory Control: Human-LLM-OR Complementarity, arXiv:2602.12631v2, p. 46, proof of Theorem 1, "The case ε = 1 is trivial: …"

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_HumanAIComp_Bound_MakarovBound

open MeasureTheory ProbabilityTheory

namespace HumanAIComp.Bound

/-- Proof of Theorem 1, Appendix K, p. 46, the case `ε = 1` (corrected): if
`ε = sup_t (F_a(t) − F_b(t + δ)) = 1`, then `b − a > δ` almost surely under every coupling of the
two laws. The printed intermediate claim "a ≤ t* a.s. and b > t* + δ a.s. for some t*" is not
stated: it fails when the supremum is not attained. -/
theorem eps_one_case (μa μb : Measure ℝ) [IsProbabilityMeasure μa] [IsProbabilityMeasure μb]
    (δ : ℝ) (hδ : 0 ≤ δ) (hε : makarovBound δ μa μb = 1) :
    ∀ π ∈ MongeKantorovichYao.transferencePlans μa μb, ∀ᵐ p ∂π, δ < p.2 - p.1 := by sorry

end HumanAIComp.Bound
