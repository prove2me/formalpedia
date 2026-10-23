-- Prove2me | Theorems.Thm_HubSpokePricing_Lagrangian_corollary_B_11
-- name    : HubSpokePricing.Lagrangian.corollary_B_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:35.268959+00:00
-- url     : https://prove2.me/theorems/dbfe05f7-69c7-4d9a-a72f-a8732dd52858
-- title:
--   Corollary B.11, p. 67 — in the original system the Lagrangian policy is unichain with recurrent class ∏_i I_i ∩ 𝒳
-- statement:
--   Throughout, $N$ is a hub-and-spoke network with one hub (location $0$), $n\ge 1$ spokes and $m$ resources. A request is of type $(i,0)$ (spoke $i$ to hub) with probability $q_{i0}>0$ and of type $(0,i)$ (hub to spoke $i$) with probability $q_{0i}>0$, these probabilities summing to one; $r_{i0},r_{0i}$ are the one-period expected revenue functions of the demand level $d\in[0,1]$, satisfying Assumption 2.1 with constants $\bar r,\bar\omega>0$.
--
--   Let $\lambda\ge0$ and for each spoke $i$ let $p_i,d_i(\cdot,i,0),d_i(\cdot,0,i)$ be an optimal solution of (6) with support $I_i$. Run the Lagrangian policy in the original system, on the states $x\in\mathcal X=\{x:\sum_ix_i\le m\}$, dropping a hub request when the hub is empty. Then the resulting Markov chain, with transition matrix $P$, has exactly one stationary distribution $\mu$,
--   $$\mu(x)>0\iff x\in\prod_{i=1}^n I_i\cap\mathcal X ,$$
--   and there is $k$ with $P^k(x,y)>0$ for every state $x\in\mathcal X$ and every $y\in\prod_iI_i\cap\mathcal X$.
--
--   The corollary says that $\prod_iI_i\cap\mathcal X$ is the single positive recurrent class, that it is aperiodic, and that all other states are transient; the stationary law is then unique and charges exactly that class. It makes $V^{\pi(\delta)}$ and $\mathbb P[X_0(\delta)=0]$ well defined, independently of the initial state.
--
--   **Formalization Note** The class structure is expressed through the stationary law (uniqueness, and support equal to $\prod_iI_i\cap\mathcal X$) and through a positive power $P^k$ from every state into that set, which on a finite chain is aperiodicity of the class plus transience of every other state.
-- source:
--   Balseiro, Brown & Chen, Dynamic Pricing of Relocating Resources in Large Networks, SSRN 3313737 (version of May 23, 2020), https://ssrn.com/abstract=3313737, p. 67, Corollary B.11

import Mathlib
import Definitions.Def_MarkovChain
import Definitions.Def_HubSpokePricing_Lagrangian_Model

namespace HubSpokePricing.Lagrangian

/-- Corollary B.11 (p. 67): under the Lagrangian policy the original system on `𝒳` has a unique
stationary distribution, positive exactly on `∏ᵢ I_i ∩ 𝒳`, and every state reaches every state
of `∏ᵢ I_i ∩ 𝒳` in exactly `k` steps for some `k`: `∏ᵢ I_i ∩ 𝒳` is the single positive recurrent
class, it is aperiodic, and all other states are transient. -/
theorem corollary_B_11 (N : Network) (hN : N.Standing) (lam : ℝ) (hlam : 0 ≤ lam)
    (sol : Fin N.n → SpokeSol N.m) (hsol : ∀ i, SpokeOptimal N lam i (sol i)) :
    (∃! μ : OrigState N → ℝ, MarkovChain.IsStationary (origKernel N sol) μ) ∧
      (∀ μ : OrigState N → ℝ, MarkovChain.IsStationary (origKernel N sol) μ →
        ∀ x : OrigState N, (0 < μ x ↔ ∀ i, 0 < (sol i).p (x.1 i))) ∧
      ∃ k : ℕ, ∀ x y : OrigState N, (∀ i, 0 < (sol i).p (y.1 i)) →
        0 < (origKernel N sol ^ k) x y := by sorry

end HubSpokePricing.Lagrangian
