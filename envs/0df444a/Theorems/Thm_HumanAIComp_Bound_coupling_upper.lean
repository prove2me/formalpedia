-- Prove2me | Theorems.Thm_HumanAIComp_Bound_coupling_upper
-- name    : HumanAIComp.Bound.coupling_upper
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:46.269986+00:00
-- url     : https://prove2.me/theorems/ddb91cf1-afe4-4619-bb0f-5b452905397c
-- title:
--   Proof of Theorem 1, Appendix K, p. 46 — coupling the remaining ε-mass arbitrarily gives a joint law with Pr(b − a > δ) ≤ ε
-- statement:
--   Let $\mu_a,\mu_b$ be probability measures on $\mathbb R$ with cumulative distribution functions $F_a,F_b$, let $\delta\ge0$ and $\varepsilon=\sup_{t\in\mathbb R}(F_a(t)-F_b(t+\delta))<1$. Let $\nu_a\le\mu_a$ and $\nu_b\le\mu_b$ be retained sub-measures of total mass $1-\varepsilon$, and let $\rho$ be a coupling of $\nu_a$ and $\nu_b$ (a measure on $\mathbb R^2$ with marginals $\nu_a,\nu_b$) under which $b-a\le\delta$ almost everywhere. Let $\sigma$ be an arbitrary coupling of the remaining masses $\mu_a-\nu_a$ and $\mu_b-\nu_b$, of total mass $\varepsilon$. Then $\rho+\sigma$ is a joint law of $(a,b)$ with marginals $\mu_a$ and $\mu_b$, and
--   $$
--   (\rho+\sigma)\bigl[\,b-a>\delta\,\bigr]\;\le\;\varepsilon .
--   $$
--   The event $\{b-a>\delta\}$ can occur only within the remaining $\varepsilon$-mass. Combined with the lower bound this gives the equality in Theorem 1.
--
--   Differences from the source:
--   - generalization: the retained masses of the proof (CDFs F_{a+}, F_{b−}) coupled monotonically → any sub-measures νa ≤ μa, νb ≤ μb of total mass 1 − ε, and any coupling ρ of them with b − a ≤ δ ρ-a.e.; reason: the step uses only these properties; the paper's retained masses and their monotone coupling (retained_split, retained_coupling) are an instance
--   - encoding: the remaining mass coupled arbitrarily; the combined coupling; Pr → any σ on ℝ × ℝ with σ.map Prod.fst = μa − νa and σ.map Prod.snd = μb − νb; ρ + σ ∈ transferencePlans μa μb; (ρ + σ).real; reason: Measure subtraction μa − νa is the removed mass since νa ≤ μa; same objects
--   - encoding: the CDFs F_a, F_b of a and b → two probability measures μa, μb on ℝ with F_a = cdf μa, F_b = cdf μb; reason: every probability law on ℝ is the law of a real random variable and conversely; same instances
--   - encoding: ε = sup_{t∈ℝ} (F_a(t) − F_b(t + δ)) → makarovBound δ μa μb = ⨆ t : ℝ, (cdf μa t − cdf μb (t + δ)); reason: the family lies in [−1, 1], so the real iSup is the true supremum; same value
-- source:
--   Baek, Fu, Ma, Peng, AI Agents for Inventory Control: Human-LLM-OR Complementarity, arXiv:2602.12631v2, p. 46, proof of Theorem 1, "Now couple the remaining mass (total probability ε) arbitrarily. … so Pr(b − a > δ) ≤ ε."

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_HumanAIComp_Bound_MakarovBound

open MeasureTheory ProbabilityTheory

namespace HumanAIComp.Bound

/-- Proof of Theorem 1, Appendix K, p. 46 (coupling the remaining mass). Let
`ε = sup_t (F_a(t) − F_b(t + δ)) < 1`, let `νa ≤ μa`, `νb ≤ μb` be retained sub-measures of total
mass `1 − ε`, coupled by `ρ` so that `b − a ≤ δ` `ρ`-a.e., and let `σ` be an arbitrary coupling of
the remaining masses `μa − νa`, `μb − νb` (total mass `ε`). Then `ρ + σ` is a joint law of `(a, b)`
with marginals `μa`, `μb`, and under it `Pr(b − a > δ) ≤ ε`. -/
theorem coupling_upper (μa μb : Measure ℝ) [IsProbabilityMeasure μa] [IsProbabilityMeasure μb]
    (δ : ℝ) (hδ : 0 ≤ δ) (hε : makarovBound δ μa μb < 1)
    (νa νb : Measure ℝ) (hνa : νa ≤ μa) (hνb : νb ≤ μb)
    (hma : νa Set.univ = ENNReal.ofReal (1 - makarovBound δ μa μb))
    (hmb : νb Set.univ = ENNReal.ofReal (1 - makarovBound δ μa μb))
    (ρ : Measure (ℝ × ℝ)) (hρa : ρ.map Prod.fst = νa) (hρb : ρ.map Prod.snd = νb)
    (hρ : ∀ᵐ p ∂ρ, p.2 - p.1 ≤ δ)
    (σ : Measure (ℝ × ℝ)) (hσa : σ.map Prod.fst = μa - νa) (hσb : σ.map Prod.snd = μb - νb) :
    ρ + σ ∈ MongeKantorovichYao.transferencePlans μa μb ∧
      (ρ + σ).real {p : ℝ × ℝ | δ < p.2 - p.1} ≤ makarovBound δ μa μb := by sorry

end HumanAIComp.Bound
