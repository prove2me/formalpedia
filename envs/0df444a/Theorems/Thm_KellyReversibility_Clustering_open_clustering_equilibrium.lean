-- Prove2me | Theorems.Thm_KellyReversibility_Clustering_open_clustering_equilibrium
-- name    : KellyReversibility.Clustering.open_clustering_equilibrium
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T03:29:20.051988+00:00
-- url     : https://prove2.me/theorems/03631343-a635-4d2c-a848-4f7c8b65bbb5
-- title:
--   Theorem 8.2 — the open clustering process has independent Poisson$(c_r)$ cluster counts and is reversible
-- statement:
--   Let cluster types $r$ range over a countable set containing the one-cluster type $1$. Consider the open clustering process with transition rates (8.3), with parameters $\lambda_{rsu}, \mu_{rsu} \ge 0$ symmetric in $r, s$, together with the immigration and emigration rates (8.7),
--   $$q(m, m + e_1) = \nu, \qquad q(m, m - e_1) = \mu m_1, \qquad \nu, \mu \ge 0,$$
--   on the state space $\mathcal S$ of all $m$ with $\sum_r m_r$ finite. Assume that every state of $\mathcal S$ can be reached from every other, and that the total rate out of every state is finite. If there exist positive numbers $c_1, c_2, \dots$ satisfying
--   $$\nu = c_1 \mu, \qquad \lambda_{rsu} c_r c_s = c_u \mu_{rsu} \qquad (8.8)$$
--   and
--   $$\sum_{r} c_r < \infty, \qquad (8.9)$$
--   then the open clustering process has equilibrium distribution
--   $$\pi(m) = \prod_{r} e^{-c_r} \frac{c_r^{m_r}}{m_r!}, \qquad (8.10)$$
--   it is reversible, and $m_1, m_2, \dots$ are independent with $m_r$ Poisson of mean $c_r$. Precisely:
--
--   1. $\pi(m) q(m, m') = \pi(m') q(m', m)$ for all $m, m' \in \mathcal S$ (detailed balance, hence reversibility);
--   2. $\pi$ satisfies the equilibrium equations $\pi(m)\sum_{m'} q(m, m') = \sum_{m'} \pi(m') q(m', m)$;
--   3. $\pi(m) > 0$ for all $m$ and $\sum_{m \in \mathcal S} \pi(m) = 1$;
--   4. for every finite set $F$ of cluster types and all $n_r \in \{0, 1, 2, \dots\}$,
--   $$\sum_{m :\, m_r = n_r \ (r \in F)} \pi(m) = \prod_{r \in F} e^{-c_r} \frac{c_r^{n_r}}{n_r!},$$
--   so that the counts $m_r$ are independent and $m_r$ has the Poisson distribution with mean $c_r$.
--
--   Opening the system removes the normalizing constant of Theorem 8.1, which is tedious to compute, and gives the equilibrium in closed form.
--
--   **Formalization Note** The statement is at the level of rates: reversibility is recorded as detailed balance for a positive normalized $\pi$ (Kelly's Theorem 1.3), and independence and the Poisson laws as the joint law of every finite set of counts; that $\pi$ is the law of a stationary Markov process with these rates is not formalized. The state space is all finitely supported vectors `R →₀ ℕ`; (8.10) is the unconditional infinite product `∏'`, and the sums are unconditional sums over the countable state space. The finiteness of the total rate out of each state is the book's standing assumption that the process stays a positive time in each state.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 164, Theorem 8.2 (with the reachability assumption stated before it)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Clustering_ClusteringRates

open KellyStochasticNetworks

namespace KellyReversibility.Clustering

theorem open_clustering_equilibrium {R : Type*} [LinearOrder R] [Countable R] (one : R)
    (lam mu : R → R → R → ℝ) (ν μ : ℝ) (c : R → ℝ)
    (hlam : ∀ r s u, 0 ≤ lam r s u) (hmu : ∀ r s u, 0 ≤ mu r s u)
    (hlam_symm : ∀ r s u, lam r s u = lam s r u) (hmu_symm : ∀ r s u, mu r s u = mu s r u)
    (hν : 0 ≤ ν) (hμ : 0 ≤ μ)
    (hfin : ∀ m, Summable (openClusterRates lam mu one ν μ m))
    (hirr : ∀ m m', Relation.ReflTransGen
      (fun a b => 0 < openClusterRates lam mu one ν μ a b) m m')
    (hc : ∀ r, 0 < c r)
    (h88_imm : ν = c one * μ)
    (h88 : ∀ r s u, lam r s u * c r * c s = c u * mu r s u)
    (h89 : Summable c) :
    DetailedBalance (openClusterPi c) (openClusterRates lam mu one ν μ) ∧
      FullBalance (openClusterPi c) (openClusterRates lam mu one ν μ) ∧
      (∀ m, 0 < openClusterPi c m) ∧
      HasSum (openClusterPi c) 1 ∧
      ∀ (F : Finset R) (n : R → ℕ),
        HasSum (fun m : R →₀ ℕ => if ∀ r ∈ F, m r = n r then openClusterPi c m else 0)
          (∏ r ∈ F, Real.exp (-c r) * c r ^ n r / ((n r).factorial : ℝ)) := by sorry

end KellyReversibility.Clustering
