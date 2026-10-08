-- Prove2me | Theorems.Thm_KellyReversibility_Symmetric_theorem_3_8
-- name    : KellyReversibility.Symmetric.theorem_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:51:45.423891+00:00
-- url     : https://prove2.me/theorems/0cff1bd7-b70c-48c9-aa66-bc768f299294
-- title:
--   Theorem 3.8 — symmetric queue with gamma-mixture service: number in queue, position classes, quasi-reversibility
-- statement:
--   Consider a stationary symmetric queue at which class-$c$ customers arrive in a Poisson stream of rate $\nu(c)$ and whose service requirement distributions are mixtures of gamma distributions: a class-$c$ customer gets the refined class $(c, z)$ with probability $p(c, z)$ and then needs $w(c, z)$ exponential stages of mean $d(c, z)$. Let $a(c) = \sum_z p(c, z) w(c, z) d(c, z)$ be the mean service requirement of class $c$, $a = \sum_c \nu(c) a(c)$, and let $b^{-1} = \sum_{n \ge 0} a^n / \prod_{l=1}^n \phi(l)$ converge. "Stationary" means the state $\mathbf c$ has the distribution $\pi$ of (3.18). Then:
--
--   0. $\pi$ is the equilibrium distribution of the Markov process $\mathbf c$ (positive, summing to unity, satisfying the equilibrium equations);
--   1. the probability that the queue contains $n$ customers is
--   $$\frac{b\,a^n}{\prod_{l=1}^n \phi(l)};$$
--   2. given there are $n$ customers in the queue, the classes of the customers are independent and the probability that the customer in a given position is of class $c$ is
--   $$\frac{\nu(c)\, a(c)}{a};$$
--   stated as: for every sequence of classes $(c_1, \dots, c_n)$, the probability that the customers in positions $1, \dots, n$ have exactly these classes is $\frac{b a^n}{\prod_{l=1}^n \phi(l)} \prod_{l=1}^n \frac{\nu(c_l) a(c_l)}{a}$;
--   3. the queue is quasi-reversible with respect to either the classification $c$ or the refined classification $(c, z)$, in the rate form (3.8), (3.10): for each class there is a rate $\alpha$ such that, from every state, the total rate of transitions to states with one more customer of that class (and the same numbers of the other classes) is $\alpha$, both for the process and for its time reversal.
--
--   Parts 1 and 2 are insensitive: they depend on the service requirement distributions only through the means $a(c)$.
--
--   **Formalization Note** Quasi-reversibility is formalized through its rate characterization (3.8), (3.10) (Kelly, p. 67), not through the independence property defining it on p. 65; that the reversed rates are those of the time-reversed stationary process is not formalized. The state space excludes records of refined classes that arrive at rate zero. Part 2 is the joint law of the class sequence, which with part 1 is the stated conditional independence.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 76–77 (PDF pp. 79–80), Theorem 3.8

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Symmetric_SymmetricQueue
import Definitions.Def_KellyReversibility_Symmetric_Equilibrium

namespace KellyReversibility.Symmetric

open Classical in
/-- Kelly 1979, Theorem 3.8 (pp. 76–77).  For a symmetric queue whose service requirements are
mixtures of gamma distributions, in equilibrium `π = (3.18)` (with `b` from (3.15)):
(0) `π` is the equilibrium distribution of the Markov process `c`;
(i) the probability that the queue contains `n` customers is `b a^n / ∏_{l=1}^n φ(l)`;
(ii) given `n`, the classes of the customers in positions `1, …, n` are independent, each of
class `c` with probability `ν(c) a(c) / a` (stated as: the probability of the class sequence
`(c_1, …, c_n)` is the probability of `n` times `∏_l ν(c_l) a(c_l) / a`);
(iii) the queue is quasi-reversible with respect to the classification `c` and with respect to
the refined classification `(c, z)`, in the rate form (3.8), (3.10). -/
theorem theorem_3_8 {C Z : Type*} [Countable C] [Countable Z]
    (Q : SymmetricQueue C Z) (hQ : Q.IsValid)
    (hmean : ∀ c, Summable (fun z => Q.p c z * (Q.w c z : ℝ) * Q.d c z))
    (hload : Summable (fun c => Q.ν c * Q.meanReq c))
    (b : ℝ) (hb : HasSum (fun n : ℕ => Q.normTerm Q.load n) b⁻¹) :
    let π : Q.State → ℝ := fun x => b * Q.eqWeight x.1
    IsEquilibriumDistribution π Q.rate ∧
    (∀ n : ℕ, HasSum (fun x : Q.State => if x.1.length = n then π x else 0)
        (b * Q.normTerm Q.load n)) ∧
    (∀ cs : List C, HasSum (fun x : Q.State => if x.1.map Customer.cls = cs then π x else 0)
        (b * Q.normTerm Q.load cs.length *
          (cs.map fun c => Q.ν c * Q.meanReq c / Q.load).prod)) ∧
    QuasiReversibleRates π Q.rate (fun x c => classCount x.1 c) ∧
    QuasiReversibleRates π Q.rate (fun x k => refinedCount x.1 k) := by sorry

end KellyReversibility.Symmetric
