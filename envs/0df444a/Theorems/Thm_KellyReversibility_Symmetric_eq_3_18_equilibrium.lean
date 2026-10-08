-- Prove2me | Theorems.Thm_KellyReversibility_Symmetric_eq_3_18_equilibrium
-- name    : KellyReversibility.Symmetric.eq_3_18_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:51:18.134508+00:00
-- url     : https://prove2.me/theorems/35b3b08a-e561-419d-bc14-1ffea366fd99
-- title:
--   Eq. (3.18) — equilibrium of a symmetric queue with gamma-mixture service requirements
-- statement:
--   Consider a symmetric queue at which class-$c$ customers arrive in a Poisson stream of rate $\nu(c)$, receive the refined class $(c, z)$ with probability $p(c, z)$, and then need $w(c, z)$ independent exponential stages of mean $d(c, z)$, so that a class-$c$ service requirement is a mixture of gamma distributions. Let
--   $$a(c) = \sum_z p(c, z)\, w(c, z)\, d(c, z), \qquad a = \sum_c \nu(c)\, a(c),$$
--   assume these series converge, and suppose $b^{-1} = \sum_{n=0}^\infty a^n / \prod_{l=1}^n \phi(l)$ (Eq. (3.15)) converges. With $\mathbf c(l) = (c(l), z(l), u(l))$ and $\mathbf c = (\mathbf c(1), \dots, \mathbf c(n))$, the equilibrium distribution of the Markov process $\mathbf c$ is
--   $$\pi(\mathbf c) = b \prod_{l=1}^n \frac{\nu(c(l))\, p(c(l), z(l))\, d(c(l), z(l))}{\phi(l)}. \tag{3.18}$$
--   That is: $\pi$ is positive on the state space, sums to unity, and satisfies the equilibrium equations for the rates of the stage description.
--
--   This is the equilibrium on which all three parts of Theorem 3.8 rest.
--
--   **Formalization Note** "Equilibrium distribution" is `IsEquilibriumDistribution`: positivity, `HasSum π 1`, convergence of the in- and out-flow series and full balance. The convergence of the series for $a(c)$ and $a$ is a hypothesis, since a divergent `tsum` would silently be $0$.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 76 (PDF p. 79), Eq. (3.18), with b from Eq. (3.15), p. 74

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Symmetric_SymmetricQueue
import Definitions.Def_KellyReversibility_Symmetric_Equilibrium

namespace KellyReversibility.Symmetric

/-- Kelly 1979, p. 76, Eq. (3.18): a symmetric queue whose service requirements are mixtures
of gamma distributions has equilibrium distribution
`π(c) = b ∏_{l=1}^n ν(c(l)) p(c(l), z(l)) d(c(l), z(l)) / φ(l)`, with `b` defined by (3.15),
`b⁻¹ = ∑_{n ≥ 0} a^n / ∏_{l=1}^n φ(l)`, `a = ∑_c ν(c) a(c)`,
`a(c) = ∑_z p(c, z) w(c, z) d(c, z)`; all these series are assumed to converge. -/
theorem eq_3_18_equilibrium {C Z : Type*} [Countable C] [Countable Z]
    (Q : SymmetricQueue C Z) (hQ : Q.IsValid)
    (hmean : ∀ c, Summable (fun z => Q.p c z * (Q.w c z : ℝ) * Q.d c z))
    (hload : Summable (fun c => Q.ν c * Q.meanReq c))
    (b : ℝ) (hb : HasSum (fun n : ℕ => Q.normTerm Q.load n) b⁻¹) :
    IsEquilibriumDistribution (fun x : Q.State => b * Q.eqWeight x.1) Q.rate := by sorry

end KellyReversibility.Symmetric
