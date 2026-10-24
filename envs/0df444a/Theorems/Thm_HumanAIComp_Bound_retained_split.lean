-- Prove2me | Theorems.Thm_HumanAIComp_Bound_retained_split
-- name    : HumanAIComp.Bound.retained_split
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:35.816913+00:00
-- url     : https://prove2.me/theorems/0a35b7fb-eb19-49c0-8ca3-113107fc08c1
-- title:
--   Proof of Theorem 1, Appendix K, p. 46 — for ε < 1, F_{a+} = max{F_a − ε, 0} and F_{b−} = min{F_b, 1 − ε} are CDFs of sub-distributions of mass 1 − ε
-- statement:
--   Let $\mu_a,\mu_b$ be probability measures on $\mathbb R$ with cumulative distribution functions $F_a,F_b$, let $\delta\ge0$, and let $\varepsilon=\sup_{t\in\mathbb R}(F_a(t)-F_b(t+\delta))<1$. Then there are measures $\nu_a\le\mu_a$ and $\nu_b\le\mu_b$ on $\mathbb R$ (the retained sub-distributions), each of total mass $1-\varepsilon$, whose distribution functions are
--   $$
--   F_{a^+}(t)=\nu_a((-\infty,t])=\max\{F_a(t)-\varepsilon,\,0\},\qquad F_{b^-}(t)=\nu_b((-\infty,t])=\min\{F_b(t),\,1-\varepsilon\}
--   $$
--   for every $t\in\mathbb R$. Thus $a^+$ removes the lower $\varepsilon$-mass of $a$ and $b^-$ removes the upper $\varepsilon$-mass of $b$; the removed parts are $\mu_a-\nu_a$ and $\mu_b-\nu_b$.
--
--   These sub-distributions are the objects coupled monotonically in the tightness proof of Theorem 1.
--
--   Differences from the source:
--   - reading: "define two sub-distributions of total mass 1 − ε: F_{a+}(t) := max{F_a(t) − ε, 0}, F_{b−}(t) := min{F_b(t), 1 − ε}"; "a+ removes the lower ε-mass of a" → there exist measures νa ≤ μa, νb ≤ μb of total mass 1 − ε with νa((−∞, t]) = max{F_a(t) − ε, 0} and νb((−∞, t]) = min{F_b(t), 1 − ε} for all t; reason: the page defines the functions and asserts they are sub-distributions obtained by removing mass from a and b; "removes mass" is read as the measure order ν ≤ μ
--   - encoding: the CDFs F_a, F_b of a and b → two probability measures μa, μb on ℝ with F_a = cdf μa, F_b = cdf μb; reason: every probability law on ℝ is the law of a real random variable and conversely; same instances
--   - encoding: ε = sup_{t∈ℝ} (F_a(t) − F_b(t + δ)) → makarovBound δ μa μb = ⨆ t : ℝ, (cdf μa t − cdf μb (t + δ)); reason: the family lies in [−1, 1], so the real iSup is the true supremum; same value
-- source:
--   Baek, Fu, Ma, Peng, AI Agents for Inventory Control: Human-LLM-OR Complementarity, arXiv:2602.12631v2, p. 46, proof of Theorem 1, "Assume ε < 1. Define two sub-distributions of total mass 1 − ε: …"

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_HumanAIComp_Bound_MakarovBound

open MeasureTheory ProbabilityTheory

namespace HumanAIComp.Bound

/-- Proof of Theorem 1, Appendix K, p. 46: for `ε = sup_t (F_a(t) − F_b(t + δ)) < 1`, the
functions `F_{a⁺}(t) = max{F_a(t) − ε, 0}` and `F_{b⁻}(t) = min{F_b(t), 1 − ε}` are the CDFs of
sub-measures `νa ≤ μa`, `νb ≤ μb` of total mass `1 − ε`. -/
theorem retained_split (μa μb : Measure ℝ) [IsProbabilityMeasure μa] [IsProbabilityMeasure μb]
    (δ : ℝ) (hδ : 0 ≤ δ) (hε : makarovBound δ μa μb < 1) :
    ∃ νa νb : Measure ℝ, νa ≤ μa ∧ νb ≤ μb ∧
      νa Set.univ = ENNReal.ofReal (1 - makarovBound δ μa μb) ∧
      νb Set.univ = ENNReal.ofReal (1 - makarovBound δ μa μb) ∧
      ∀ t : ℝ, νa.real (Set.Iic t) = max (cdf μa t - makarovBound δ μa μb) 0 ∧
        νb.real (Set.Iic t) = min (cdf μb t) (1 - makarovBound δ μa μb) := by sorry

end HumanAIComp.Bound
