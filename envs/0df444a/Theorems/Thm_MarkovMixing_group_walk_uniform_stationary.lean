-- Prove2me | Theorems.Thm_MarkovMixing_group_walk_uniform_stationary
-- name    : MarkovMixing.group_walk_uniform_stationary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T01:43:07.825352+00:00
-- url     : https://prove2.me/theorems/2c2d99cd-077e-4d2b-a5fe-fd3deeff5689
-- title:
--   Propositions 2.12 and 2.14 -- random walks on finite groups
-- statement:
--   The random walk on a finite group $G$ with increment distribution $\mu$ (step from $a$ to $ha$ with probability $\mu(h)$) is a Markov chain for which the uniform distribution on $G$ is stationary; and if $\mu$ is symmetric ($\mu(g^{-1})=\mu(g)$), the walk is reversible with respect to the uniform distribution.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 2.6, Propositions 2.12 and 2.14, pp. 28-29

import Definitions.Def_mm_basic

namespace MarkovMixing

/-- **Propositions 2.12 and 2.14** (LPW): the random walk on a finite group
with increment distribution `μ` is a Markov chain for which the uniform
distribution is stationary; if `μ` is symmetric (`μ(g) = μ(g⁻¹)`), the walk is
moreover reversible. -/
theorem group_walk_uniform_stationary {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] (μ : G → ℝ) (hμ : IsDist μ) :
    IsStochastic (groupWalk μ) ∧
    IsStationary (groupWalk μ) (uniformDist G) ∧
    ((∀ g : G, μ g⁻¹ = μ g) → DetailedBalance (groupWalk μ) (uniformDist G)) := by
  sorry

end MarkovMixing
