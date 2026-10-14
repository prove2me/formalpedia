-- Prove2me | Theorems.Thm_GDPRPrivacy_ProfitGain_lemmaA3_case1a_case2a
-- name    : GDPRPrivacy.ProfitGain.lemmaA3_case1a_case2a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:25.287005+00:00
-- url     : https://prove2.me/theorems/8cd3862a-9e90-4416-b59e-ded3bffd605f
-- title:
--   Lemma A3, first bullet, p. 33 — for x ≤ 1/2 and α < α₁(x), case 1a equilibrium before the GDPR and case 2a after
-- statement:
--   Consider the model with opt-in benefit $x\in(0,1)$ and data revenue $\alpha\ge 0$ per unit of collected data. Let $\widehat\Pi$ and $\widetilde\Pi$ be the firm's profit before and after the GDPR, as functions of the price $p\in\mathbb R$. An equilibrium price is a global maximizer of the profit over $\mathbb R$.
--
--   Suppose $x\le 1/2$ and $\alpha<\alpha_1(x)=\max\{(1-2x)/2,0\}$. Then both regimes have an equilibrium price. Before the GDPR the equilibrium is of case 1a and after the GDPR it is of case 2a:
--   $$
--   x<\widehat p^\star<1+x\qquad\text{and}\qquad x<\widetilde p^\star<1+x
--   $$
--   for every maximizer $\widehat p^\star$ of $\widehat\Pi$ and every maximizer $\widetilde p^\star$ of $\widetilde\Pi$.
--
--   With $v(p)=p-x$, case 1a is the regime $0<v(\widehat p^\star)<1$ before the GDPR and case 2a is the regime $0<v(\widetilde p^\star)<1$ after it. In both, consumers with valuation below $v(p)$ do not buy, so the market is not fully covered. This lemma identifies the regime in which the closed-form equilibrium profits $\widehat\Pi^\star_{1a}$ and $\widetilde\Pi^\star_{2a}$ apply.
--
--   **Formalization Note.** Equilibrium prices are global maximizers on `Set.univ` (`IsMaxOn`). The statement asserts existence of a maximizer in each regime, so the case claims are not vacuous. The paper's "case 1a / case 2a" are encoded by the price intervals of pp. 10 and 13 ($0<v(p)<1$ with $v(p)=p-x$). The standing assumptions $0<x<1$ and $\alpha\ge 0$ are hypotheses.
-- source:
--   Choe, Matsushima & Shekhar, The Bright Side of the GDPR, ISER DP No. 1246 (June 2024), p. 33, Lemma A3 (first bullet); case intervals pp. 10, 13

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model

namespace GDPRPrivacy.ProfitGain

/-- Lemma A3, first bullet (p. 33): if `x ≤ 1/2` and `α < α₁(x)`, the equilibrium before the GDPR
is a case 1a equilibrium (`x < p̂⋆ < 1 + x`) and the equilibrium after the GDPR is a case 2a
equilibrium (`x < p̃⋆ < 1 + x`). Equilibrium prices are global maximizers of profit over all of `ℝ`;
both exist, and every maximizer lies in the stated case interval. -/
theorem lemmaA3_case1a_case2a (x α : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hα : 0 ≤ α)
    (hxhalf : x ≤ 1 / 2) (hα1 : α < GDPRPrivacy.PriceRise.alpha1 x) :
    (∃ p, IsMaxOn (GDPRPrivacy.PriceRise.profitBefore x α) Set.univ p) ∧
    (∀ p, IsMaxOn (GDPRPrivacy.PriceRise.profitBefore x α) Set.univ p → x < p ∧ p < 1 + x) ∧
    (∃ p, IsMaxOn (GDPRPrivacy.PriceRise.profitAfter x α) Set.univ p) ∧
    (∀ p, IsMaxOn (GDPRPrivacy.PriceRise.profitAfter x α) Set.univ p → x < p ∧ p < 1 + x) := by sorry

end GDPRPrivacy.ProfitGain
