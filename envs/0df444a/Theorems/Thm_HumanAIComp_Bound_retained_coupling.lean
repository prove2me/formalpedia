-- Prove2me | Theorems.Thm_HumanAIComp_Bound_retained_coupling
-- name    : HumanAIComp.Bound.retained_coupling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:36.208146+00:00
-- url     : https://prove2.me/theorems/506caac0-2e48-47b4-9d6a-c0274a4ca681
-- title:
--   Proof of Theorem 1, Appendix K, p. 46 — the retained masses can be coupled so that b − a ≤ δ almost surely (monotone coupling)
-- statement:
--   Let $\delta\ge0$ and let $\nu_a,\nu_b$ be finite measures on $\mathbb R$ of equal total mass such that
--   $$
--   \nu_a((-\infty,t])\;\le\;\nu_b((-\infty,t+\delta])\qquad\text{for every } t\in\mathbb R ,
--   $$
--   that is, after normalisation, the law of $a$ dominates the law of $b-\delta$ in the first-order stochastic order. Then there is a measure $\rho$ on $\mathbb R^2$ with first marginal $\nu_a$ and second marginal $\nu_b$ under which $b-a\le\delta$ (equivalently $a\ge b-\delta$) holds $\rho$-almost everywhere.
--
--   In the proof of Theorem 1 this is applied to the retained sub-distributions $\nu_a,\nu_b$ of total mass $1-\varepsilon$, for which the hypothesis is the inequality $F_{a^+}(t)\le F_{b^-}(t+\delta)$. The paper invokes the monotone coupling theorem; its probability-measure form is on the platform as `StochasticOrders.Usual.usual_order_coupling_iff_v2`.
--
--   Differences from the source:
--   - generalization: the retained sub-distributions with CDFs F_{a+}, F_{b−} of mass 1 − ε (after normalising by 1 − ε) → any two finite measures νa, νb on ℝ of equal total mass with νa((−∞, t]) ≤ νb((−∞, t + δ]) for all t (no normalisation); reason: the step uses only equal mass and the CDF inequality; it specialises to the paper's retained masses via retained_split and retained_cdf_le, and for positive mass the unnormalised inequality is equivalent to the normalised one
--   - encoding: a coupling of the retained masses → a measure ρ on ℝ × ℝ with ρ.map Prod.fst = νa, ρ.map Prod.snd = νb; "almost surely" as ∀ᵐ p ∂ρ; reason: same object for finite measures
-- source:
--   Baek, Fu, Ma, Peng, AI Agents for Inventory Control: Human-LLM-OR Complementarity, arXiv:2602.12631v2, p. 46, proof of Theorem 1, "Normalizing by 1 − ε, … the retained masses can therefore be coupled so that a ≥ b − δ, equivalently b − a ≤ δ, almost surely."

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_HumanAIComp_Bound_MakarovBound

open MeasureTheory ProbabilityTheory

namespace HumanAIComp.Bound

/-- Proof of Theorem 1, Appendix K, p. 46 (monotone coupling of the retained masses), stated for
any two finite measures of equal total mass: if `νa((−∞, t]) ≤ νb((−∞, t + δ])` for every `t`
(the law of `a` dominates that of `b − δ` in the first order), then `νa` and `νb` admit a coupling
`ρ` (a measure on `ℝ × ℝ` with marginals `νa`, `νb`) under which `b − a ≤ δ` almost everywhere. -/
theorem retained_coupling (δ : ℝ) (hδ : 0 ≤ δ) (νa νb : Measure ℝ) [IsFiniteMeasure νa]
    (hmass : νa Set.univ = νb Set.univ)
    (hdom : ∀ t : ℝ, νa (Set.Iic t) ≤ νb (Set.Iic (t + δ))) :
    ∃ ρ : Measure (ℝ × ℝ), ρ.map Prod.fst = νa ∧ ρ.map Prod.snd = νb ∧
      ∀ᵐ p ∂ρ, p.2 - p.1 ≤ δ := by sorry

end HumanAIComp.Bound
