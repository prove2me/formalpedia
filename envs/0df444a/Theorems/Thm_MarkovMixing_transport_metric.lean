-- Prove2me | Theorems.Thm_MarkovMixing_transport_metric
-- name    : MarkovMixing.transport_metric
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:24:47.249394+00:00
-- url     : https://prove2.me/theorems/f0898918-45f5-42d4-a649-d09970652839
-- title:
--   The transportation metric is an attained metric
-- statement:
--   Let $\rho$ be a metric on a finite state space $V$ — nonnegative, vanishing exactly on the diagonal, symmetric, and satisfying the triangle inequality — and let $\mu,\nu,\eta$ be probability distributions on $V$. A **coupling** of $\mu$ and $\nu$ is a probability distribution $q$ on ordered pairs with marginals $\mu$ and $\nu$, and the **transportation distance** (Kantorovich distance) is the cheapest expected cost of moving $\mu$ onto $\nu$:
--   $$\rho_K(\mu,\nu)=\inf\Bigl\{\sum_{x,y}\rho(x,y)\,q(x,y)\;:\;q\ \text{a coupling of}\ \mu,\nu\Bigr\}.$$
--
--   The theorem (Lemma 14.3 and Remark 14.2 of Levin–Peres–Wilmer) asserts:
--
--   1. the infimum is attained: some coupling $q$ realizes $\rho_K(\mu,\nu)$ exactly — an **optimal coupling** exists;
--   2. $\rho_K$ satisfies the triangle inequality: $\rho_K(\mu,\eta)\le\rho_K(\mu,\nu)+\rho_K(\nu,\eta)$.
--
--   Attainment is a compactness statement about the coupling polytope; the triangle inequality is proved by gluing an optimal coupling of $(\mu,\nu)$ with one of $(\nu,\eta)$ along their common marginal. Together they make $\rho_K$ a genuine metric on distributions — the metric in which the path coupling theorem measures contraction.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 14.1, Lemma 14.3 and Remark 14.2, p. 190

import Definitions.Def_mm_transport

namespace MarkovMixing

/-- **Lemma 14.3 and Remark 14.2** (LPW): the transportation distance is
attained by an optimal coupling, and satisfies the triangle inequality. -/
theorem transport_metric {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : V → V → ℝ) (hρ0 : ∀ x y : V, 0 ≤ ρ x y)
    (hρeq : ∀ x y : V, ρ x y = 0 ↔ x = y)
    (hρsymm : ∀ x y : V, ρ x y = ρ y x)
    (hρtri : ∀ x y z : V, ρ x z ≤ ρ x y + ρ y z)
    (μ ν η : V → ℝ) (hμ : IsDist μ) (hν : IsDist ν) (hη : IsDist η) :
    (∃ q : V × V → ℝ, IsCoupling μ ν q ∧
      transportDist ρ μ ν = ∑ p : V × V, ρ p.1 p.2 * q p) ∧
    transportDist ρ μ η ≤ transportDist ρ μ ν + transportDist ρ ν η := by
  sorry

end MarkovMixing
