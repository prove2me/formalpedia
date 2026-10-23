-- Prove2me | Theorems.Thm_HubSpokePricing_Lagrangian_corollary_B_10
-- name    : HubSpokePricing.Lagrangian.corollary_B_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:32.336242+00:00
-- url     : https://prove2.me/theorems/69fd2975-151a-4367-9f26-ba5739db1083
-- title:
--   Corollary B.10, pp. 66–67 — in the relaxation the Lagrangian policy attains V̄^λ, ∏_i I_i is its aperiodic recurrent class, and ∏_i p_i(x_i) its unique stationary law
-- statement:
--   Throughout, $N$ is a hub-and-spoke network with one hub (location $0$), $n\ge 1$ spokes and $m$ resources. A request is of type $(i,0)$ (spoke $i$ to hub) with probability $q_{i0}>0$ and of type $(0,i)$ (hub to spoke $i$) with probability $q_{0i}>0$, these probabilities summing to one; $r_{i0},r_{0i}$ are the one-period expected revenue functions of the demand level $d\in[0,1]$, satisfying Assumption 2.1 with constants $\bar r,\bar\omega>0$.
--
--   Let $\lambda\ge0$ and for each spoke $i$ let $p_i,d_i(\cdot,i,0),d_i(\cdot,0,i)$ be an optimal solution of (6). Run the Lagrangian policy (Definition 3.1) in the relaxed system, whose states are the spoke levels $x\in\bar{\mathcal X}=\{x:0\le x_i\le m\}$ and in which hub requests are never dropped, and let $P$ be the transition matrix of the resulting Markov chain. Then:
--
--   1. the policy is optimal to the Lagrangian relaxation: its long-run revenue net of the penalty $\lambda(\sum_ix_i-m)$ under $q$ equals $\bar V^\lambda=m\lambda+\sum_ih_i^\lambda$,
--   $$\sum_{x\in\bar{\mathcal X}}q(x)\Big(\sum_{i}\big[q_{i0}r_{i0}(d_i(x_i,i,0))+q_{0i}r_{0i}(d_i(x_i,0,i))\big]-\lambda\sum_ix_i\Big)+m\lambda=\bar V^\lambda;$$
--   2. there is $k$ with $P^k(x,y)>0$ for every state $x$ and every $y\in\prod_iI_i$ ($I_i$ the support of $p_i$): $\prod_i I_i$ is the single recurrent class, it is aperiodic, and all other states are transient;
--   3. $$q(x)=\prod_{i=1}^n p_i(x_i)$$
--   is a stationary distribution of the chain, and it is the only one.
--
--   Independence across spokes in the relaxed system is what makes the hub level $m-\sum_i\tilde X_i(\delta)$ a sum of independent log-concave variables, the input of Proposition 4.6.
--
--   **Formalization Note** The relaxation's optimal value is $\bar V^\lambda$ of (4) (Proposition 3.1), so optimality of the policy is stated as attaining it; the controls are those of Definition 3.1 (the stored values on $I_i$). On a finite chain, "a single recurrent class $C$, aperiodic, all other states transient" is the statement that some power $P^k$ is positive from every state into $C$, together with the stationary law charging exactly $C$ (here $q>0$ exactly on $\prod_iI_i$). Stationarity is `MarkovChain.IsStationary`: a probability vector $\mu$ with $\mu P=\mu$.
-- source:
--   Balseiro, Brown & Chen, Dynamic Pricing of Relocating Resources in Large Networks, SSRN 3313737 (version of May 23, 2020), https://ssrn.com/abstract=3313737, pp. 66–67, Corollary B.10, (66)

import Mathlib
import Definitions.Def_MarkovChain
import Definitions.Def_HubSpokePricing_Lagrangian_Model

namespace HubSpokePricing.Lagrangian

/-- Corollary B.10 (pp. 66–67): under the Lagrangian policy built from optimal solutions of (6),
(a) the policy attains `V̄^λ = mλ + ∑ᵢ h_i^λ` in the Lagrangian relaxation (its long-run revenue
net of the penalty `λ(∑ᵢ xᵢ − m)` under its stationary law equals `V̄^λ`); (b) every state reaches
every state of `∏ᵢ I_i` in exactly `k` steps for some `k` (`∏ᵢ I_i` is the single recurrent
class, aperiodic, and all other states are transient); (c) the relaxed system on `𝒳̄` has the
unique stationary distribution `q(x) = ∏ᵢ p_i(x_i)`. -/
theorem corollary_B_10 (N : Network) (hN : N.Standing) (lam : ℝ) (hlam : 0 ≤ lam)
    (sol : Fin N.n → SpokeSol N.m) (hsol : ∀ i, SpokeOptimal N lam i (sol i)) :
    (∑ x : RelaxState N, prodLaw N sol x *
        (∑ i, (N.qOut i * N.rOut i (lagOut (sol i) (x i : ℕ)) +
            N.qIn i * N.rIn i (lagIn (sol i) (x i : ℕ))) -
          lam * ∑ i, (((x i : ℕ)) : ℝ)) + N.m * lam = Vbar N lam) ∧
    (∃ k : ℕ, ∀ x y : RelaxState N, (∀ i, 0 < (sol i).p (y i)) →
        0 < (relaxKernel N sol ^ k) x y) ∧
    MarkovChain.IsStationary (relaxKernel N sol) (prodLaw N sol) ∧
      ∀ μ : RelaxState N → ℝ, MarkovChain.IsStationary (relaxKernel N sol) μ →
        μ = prodLaw N sol := by sorry

end HubSpokePricing.Lagrangian
