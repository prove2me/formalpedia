-- Prove2me | Theorems.Thm_InfluencerAuth_Switch_proposition_1
-- name    : InfluencerAuth.Switch.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:30.831015+00:00
-- url     : https://prove2.me/theorems/b2be90aa-70f2-4a37-adfb-3318709db742
-- title:
--   Proposition 1, p. 6 — the optimal policy: always authentic if γφ ≤ 1, always inauthentic without Condition 1, else authentic until the threshold of (3), then inauthentic
-- statement:
--   Let $0<\gamma<1$, $\varphi>1$, $\beta>0$ and $r>0$. Let $m(A)$ be the integral (3), the derivative of the value of always being inauthentic, and let Condition 1 be as in footnote 4. Then:
--
--   1. if $\gamma\varphi\le1$, then for every initial awareness $A_0\in(0,1)$ always being authentic is optimal;
--   2. if $\gamma\varphi>1$ and Condition 1 fails, then for every $A_0\in(0,1)$ always being inauthentic is optimal;
--   3. if $\gamma\varphi>1$ and Condition 1 holds, there is an awareness level $A^*\in(0,1)$ with
--   $$
--   m(A^*)=\frac{\gamma\varphi-1}{(1-\gamma)\beta(1-A^*)},
--   $$
--   and a level $\bar A>0$ such that for every initial awareness $A_0\in(0,1)$ with $A_0<\bar A$ the feedback policy "authentic while $A_t<A^*$, inauthentic once $A_t\ge A^*$" is optimal: there is an admissible path $A$ from $A_0$, driven by the policy $S=\{t\ge0: A_t\ge A^*\}$ of that same path, which is optimal from $A_0$.
--
--   Proposition 1 is the paper's main characterization of the influencer's dynamic trade-off between growing (authentic, faster awareness growth) and monetizing (inauthentic, higher current profit): a small influencer with enough growth potential grows first and monetizes permanently once her marginal value of awareness falls to the profit gain from inauthenticity.
--
--   **Formalization Note** "The influencer is always authentic / inauthentic" is read as optimality of the corresponding constant policy against every measurable policy; at $\gamma\varphi=1$ authenticity is weakly optimal. "Initial awareness sufficiently small" is the existence of the bound $\bar A$. The paper's "value function derivative stated in (3)" is the integral $m$ (definition `margValue`); that it is the derivative of the always-inauthentic value is the milestone (3). Awareness never decreases along an admissible path, so the switching set is a half-line and the switch is permanent. The discount rate is assumed positive, the reading of "discount rate $r$" that makes (2) finite.
-- source:
--   Nistor, Selove, Villas-Boas, Management Science (Articles in Advance 2024), Proposition 1, p. 6

import Mathlib
import Definitions.Def_InfluencerAuth_Switch_Model
import Definitions.Def_InfluencerAuth_Switch_ClosedForms

open MeasureTheory Set Filter Topology

namespace InfluencerAuth.Switch

/-- Proposition 1 (p. 6). -/
theorem proposition_1 (γ φ β r : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hφ : 1 < φ)
    (hβ : 0 < β) (hr : 0 < r) :
    (γ * φ ≤ 1 →
      ∀ A₀ ∈ Set.Ioo (0 : ℝ) 1, ∃ A : ℝ → ℝ, IsOptimalFrom β γ φ r A₀ ∅ A) ∧
    (1 < γ * φ → ¬ Condition1 γ φ β r →
      ∀ A₀ ∈ Set.Ioo (0 : ℝ) 1, ∃ A : ℝ → ℝ, IsOptimalFrom β γ φ r A₀ Set.univ A) ∧
    (1 < γ * φ → Condition1 γ φ β r →
      ∃ Astar ∈ Set.Ioo (0 : ℝ) 1,
        margValue γ φ β r Astar = (γ * φ - 1) / ((1 - γ) * β * (1 - Astar)) ∧
        ∃ Abar : ℝ, 0 < Abar ∧ ∀ A₀ ∈ Set.Ioo (0 : ℝ) 1, A₀ < Abar →
          ∃ A : ℝ → ℝ, IsOptimalFrom β γ φ r A₀ {t : ℝ | 0 ≤ t ∧ Astar ≤ A t} A) := by sorry

end InfluencerAuth.Switch
