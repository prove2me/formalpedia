-- Prove2me | Theorems.Thm_KellyReversibility_Symmetric_eq_3_14_equilibrium
-- name    : KellyReversibility.Symmetric.eq_3_14_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:51:28.918244+00:00
-- url     : https://prove2.me/theorems/a68b145e-318b-4aec-937d-318c61ce9de5
-- title:
--   Eqs. (3.14)–(3.15) — equilibrium of a symmetric queue with gamma service requirements
-- statement:
--   Consider a symmetric queue (positions $1, \dots, n$, effort $\phi(n)$ split by $\gamma(l, n)$, arrivals placed by the same $\gamma(l, n+1)$) at which customers of class $c$ arrive in a Poisson stream of rate $\nu(c)$ and need $w(c) \ge 1$ independent exponential stages of service, each of mean $d(c) > 0$. The state is $\mathbf c = (\mathbf c(1), \dots, \mathbf c(n))$ with $\mathbf c(l) = (c(l), u(l))$, $u(l)$ the stage in progress. Let
--   $$a = \sum_c \nu(c) d(c) w(c)$$
--   and suppose the normalizing constant $b$ given by
--   $$b^{-1} = \sum_{n=0}^\infty \frac{a^n}{\prod_{l=1}^n \phi(l)} \tag{3.15}$$
--   is positive, i.e. the series converges. Then the equilibrium distribution of $\mathbf c$ is
--   $$\pi(\mathbf c) = b \prod_{l=1}^n \frac{\nu(c(l))\, d(c(l))}{\phi(l)}. \tag{3.14}$$
--   That is: $\pi$ is positive, sums to unity over the state space, and satisfies the equilibrium equations.
--
--   This is the case of the gamma-mixture model in which each class has a single refinement; it shows the stationary law depends on the stage structure only through $d(c)w(c)$ once the stages are summed out.
--
--   **Formalization Note** The model is `SymmetricQueue C Unit`: the refined-class set is a one-point type, so $p(c, \cdot) = 1$ and $w(c), d(c)$ are `w c ()`, `d c ()`. The constants $a$ and $b$ are carried through `HasSum` hypotheses, which also assert convergence.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 74 (PDF p. 77), Eqs. (3.14)–(3.15)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Symmetric_SymmetricQueue
import Definitions.Def_KellyReversibility_Symmetric_Equilibrium

namespace KellyReversibility.Symmetric

/-- Kelly 1979, p. 74, Eqs. (3.14)–(3.15): a symmetric queue whose class-`c` customers need
`w(c)` exponential stages of mean `d(c)` (no refinement: the refined-class type is `Unit`) has
equilibrium distribution `π(c) = b ∏_{l=1}^n ν(c(l)) d(c(l)) / φ(l)`, provided
`b⁻¹ = ∑_{n ≥ 0} a^n / ∏_{l=1}^n φ(l)` converges, where `a = ∑_c ν(c) d(c) w(c)`. -/
theorem eq_3_14_equilibrium {C : Type*} [Countable C] (Q : SymmetricQueue C Unit)
    (hQ : Q.IsValid) (a : ℝ) (ha : HasSum (fun c => Q.ν c * Q.d c () * (Q.w c () : ℝ)) a)
    (b : ℝ) (hb : HasSum (fun n : ℕ => a ^ n / ∏ l ∈ Finset.Icc 1 n, Q.φ l) b⁻¹) :
    IsEquilibriumDistribution
      (fun x : Q.State => b * ∏ i : Fin x.1.length,
        Q.ν (x.1.get i).cls * Q.d (x.1.get i).cls () / Q.φ ((i : ℕ) + 1))
      Q.rate := by sorry

end KellyReversibility.Symmetric
