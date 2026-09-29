-- Prove2me | Theorems.Thm_MarkovMixing_thomson_principle
-- name    : MarkovMixing.thomson_principle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T21:00:23.783964+00:00
-- url     : https://prove2.me/theorems/0b8afd78-5f55-4f42-9ac5-356c8083666d
-- title:
--   Theorem 9.10 -- Thomson's principle
-- statement:
--   Let $c$ be a **network** on a finite vertex set: a symmetric nonnegative conductance function with total conductance $c(x)=\sum_yc(x,y)>0$ at every vertex, whose associated walk $P(x,y)=c(x,y)/c(x)$ is irreducible. Fix distinct vertices $a\ne z$. A **flow** from $a$ to $z$ is an antisymmetric edge function $\theta(x,y)=-\theta(y,x)$ vanishing wherever $c$ does, satisfying the node law $\sum_y\theta(x,y)=0$ at every vertex except $a$ and $z$; its **strength** is the net flux $\sum_y\theta(a,y)$ out of $a$, and a flow of strength one is a **unit flow**. The **energy** of a flow is
--   $$\mathcal E(\theta)=\frac12\sum_{x,y}\frac{\theta(x,y)^2}{c(x,y)},$$
--   each undirected edge counted once. The **effective resistance** $R(a\leftrightarrow z)$ is defined through the voltage $W(x)=\mathbb P_x\{\tau_a<\tau_z\}$ and the current $\|I\|=\sum_yc(a,y)[W(a)-W(y)]$ as $R(a\leftrightarrow z)=\|I\|^{-1}$.
--
--   The theorem (**Thomson's Principle**, Theorem 9.10 of Levin–Peres–Wilmer) asserts:
--
--   1. $R(a\leftrightarrow z)=\inf\{\mathcal E(\theta):\theta\ \text{a unit flow from}\ a\ \text{to}\ z\}$;
--   2. the infimum is attained — some unit flow (the current flow) has energy exactly $R(a\leftrightarrow z)$.
--
--   Resistance is a variational quantity: any unit flow certifies an upper bound on it, which is the source of all flow-based hitting-time estimates.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 9.4, Theorem 9.10, p. 121

import Definitions.Def_mm_network

namespace MarkovMixing

/-- **Theorem 9.10, Thomson's Principle** (LPW): for a connected network,
the effective resistance is the minimal energy of a unit flow from `a` to
`z`, and the minimum is attained. -/
theorem thomson_principle {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (hc : IsConductance c)
    (hpos : ∀ x : V, 0 < vertexConductance c x)
    (hirr : Irreducible (networkWalk c)) (a z : V) (haz : a ≠ z) :
    effectiveResistance c a z =
      sInf {r : ℝ | ∃ θ : V → V → ℝ,
        IsFlow c θ a z ∧ flowStrength θ a = 1 ∧ r = flowEnergy c θ} ∧
    ∃ θ : V → V → ℝ, IsFlow c θ a z ∧ flowStrength θ a = 1 ∧
      effectiveResistance c a z = flowEnergy c θ := by
  sorry

end MarkovMixing
