-- Prove2me | Theorems.Thm_MFEUnique_Uniq_theorem_1
-- name    : MFEUnique.Uniq.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:09.477465+00:00
-- url     : https://prove2.me/theorems/b20806e6-ae08-4d11-b35b-d71beff3732e
-- title:
--   Theorem 1, p. 13 — if Q is X-ergodic, increasing in x and decreasing in s, and ⪰ is complete and agrees with ⪰SD, there is at most one MFE
-- statement:
--   Consider an anonymous stochastic game with compact metric state space $X$ carrying a closed partial order, action set $A \subseteq \mathbb R^q$, feasible correspondence $\Gamma$, payoff $\pi$, transition $w$, finitely valued i.i.d. shock with probabilities $p_1, \dots, p_J$ and discount factor $0 < \beta < 1$, satisfying Assumption 1 ($\pi$ bounded and jointly continuous, $w$ jointly continuous, $\Gamma$ compact-valued and continuous). Let $\succeq$ be a binary relation on $\mathcal P(X)$ such that $s_2 \sim s_1$ implies $\pi(\cdot,\cdot,s_1) = \pi(\cdot,\cdot,s_2)$ and $w(\cdot,\cdot,s_1,\cdot) = w(\cdot,\cdot,s_2,\cdot)$.
--
--   Suppose Assumption 2 holds:
--
--   1. the kernel $Q = Q_g$ of the optimal strategy is $X$-ergodic, increasing in $x$ and decreasing in $s$;
--   2. $\succeq$ agrees with $\succeq_{SD}$;
--   3. the optimal strategy correspondence $G$ is single-valued, with selection $g$.
--
--   If $\succeq$ is complete, then if a mean field equilibrium exists, it is unique: for any two MFEs $(g_1, s_1)$ and $(g_2, s_2)$,
--   $$s_1 = s_2.$$
--
--   This is the main theorem of the paper. It reduces the uniqueness of a stationary equilibrium of a large dynamic game to monotonicity properties of a single player's optimally controlled Markov kernel, and it is the basis of the paper's comparative statics results and of its applications to dynamic oligopoly and heterogeneous-agent macroeconomic models.
--
--   **Formalization Note** "If an MFE exists, it is unique" is stated as "any two MFEs have the same population state"; existence is neither assumed nor concluded. Each MFE carries its own optimal strategy $g_i$, which by single-valuedness of $G$ equals $g$ at $s_i$. The relation $\succeq$ is an arbitrary predicate (not assumed reflexive, transitive or antisymmetric). $\succeq_{SD}$ is `StochLE` with swapped arguments: `StochLE P₁ P₂` reads "$P_2 \succeq_{SD} P_1$". The value function is the supremum over measurable history-dependent strategies (see `MFEUnique.Uniq.Game` for the time and expectation conventions).
-- source:
--   Light and Weintraub, Mean Field Equilibrium: Uniqueness, Existence, and Comparative Statics, arXiv:1903.02273v3, p. 13, Theorem 1 with Assumption 2 (standing assumptions: Assumption 1, pp. 7–8; the relation ⪰, p. 12; proof pp. 13–14)

import Mathlib
import Definitions.Def_MFEUnique_Uniq_Equilibrium

open MeasureTheory

namespace MFEUnique.Uniq

/-- Theorem 1 (Light–Weintraub, arXiv:1903.02273v3, p. 13): suppose Assumption 2 holds
(`Q` is `X`-ergodic, increasing in `x` and decreasing in `s`; `⪰` agrees with `⪰SD`; `G` is
single-valued with selection `g`). If the binary relation `⪰` is complete, then if an MFE exists,
it is unique: any two MFEs have the same population state. -/
theorem theorem_1 {X : Type*} [MetricSpace X] [CompactSpace X] [PartialOrder X]
    [OrderClosedTopology X] [MeasurableSpace X] [BorelSpace X]
    {q J : ℕ} {A : Set (EuclideanSpace ℝ (Fin q))} {E : Type*} [TopologicalSpace E]
    (G : Game X q J E A) (hG : G.Standing)
    (R : ProbabilityMeasure X → ProbabilityMeasure X → Prop) (hR : G.RelStanding R)
    (hagree : AgreesSD R) (hcomplete : IsComplete R)
    (g : X → ProbabilityMeasure X → A) (hg : ∀ x s, g x s ∈ G.Gopt x s)
    (hsingle : ∀ x s a, a ∈ G.Gopt x s → a = g x s)
    (herg : G.IsXErgodic g) (hinc : G.IncreasingInX g) (hdec : G.DecreasingInS R g) :
    ∀ (g₁ g₂ : X → ProbabilityMeasure X → A) (s₁ s₂ : ProbabilityMeasure X),
      G.IsMFE g₁ s₁ → G.IsMFE g₂ s₂ → s₁ = s₂ := by sorry

end MFEUnique.Uniq
