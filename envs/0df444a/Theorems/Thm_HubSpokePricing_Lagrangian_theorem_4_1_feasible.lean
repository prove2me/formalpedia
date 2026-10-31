-- Prove2me | Theorems.Thm_HubSpokePricing_Lagrangian_theorem_4_1_feasible
-- name    : HubSpokePricing.Lagrangian.theorem_4_1_feasible
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-30T19:06:17.372472+00:00
-- url     : https://prove2.me/theorems/d00e0070-4fdf-4eb3-87ce-95cbc393d6ef
-- title:
--   Theorem 4.1 (first inequality), p. 17 — the Lagrangian policy is feasible: V^π ≤ V^OPT
-- statement:
--   Let $N$ be a hub-and-spoke network satisfying the standing assumptions (Assumption 2.1): one hub, $n\ge1$ spokes, $m$ resources, request probabilities $q_{i0},q_{0i}>0$ summing to one, and revenue functions $r_{i0},r_{0i}$. Fix a dual price $\lambda\ge0$ and, for every spoke $i$, an optimal solution $(p_i,d_i)$ of the spoke problem (6) at $\lambda$. Let $\pi$ be the resulting Lagrangian policy (Definition 3.1), run in the **original** system on $\mathcal X=\{x\in\mathbb N^n:\sum_ix_i\le m\}$. Let $\mu$ be a stationary distribution of that Markov chain, and let
--   $$V^{\pi}=\sum_{x\in\mathcal X}\mu(x)\sum_{s}q_s\,r_s\big(d^\pi(x,s)\big)$$
--   be the corresponding stationary average revenue.
--
--   Then for every initial state $x^0\in\mathcal X$,
--   $$V^{\pi}\le V^{\mathrm{OPT}}(x^0),$$
--   where $V^{\mathrm{OPT}}(x^0)$ is the optimal long-run average revenue of problem (1). It is defined as the supremum, over feasible non-anticipative pricing policies, of the $\limsup$ of the $T$-period average expected revenue.
--
--   This is the first inequality of Theorem 4.1. The paper justifies it in one line, "because our policy is feasible". Behind that line are two facts. The Lagrangian policy never serves a request whose origin is empty. By Corollary B.11, the original system under it has a single recurrent class and a unique stationary distribution, so its long-run average revenue from any initial state equals $V^\pi$.
--
--   **Formalization Note.** $V^{\pi}$ is `Vpi N sol μ` for an arbitrary stationary `μ` of `origKernel N sol`. $V^{\mathrm{OPT}}$ is `VOPT N x0`: an `iSup` of a `limsup` over history-dependent policies that satisfy `Feasible`. The statement is the first conjunct of `theorem_4_1`. Unlike that theorem, it needs no $\delta$: it holds for any $\lambda\ge0$ with optimal spoke solutions.
-- source:
--   Balseiro, Brown & Chen, Dynamic Pricing of Relocating Resources in Large Networks, SSRN 3313737 (version of May 23, 2020), https://ssrn.com/abstract=3313737, p. 17, Theorem 4.1 (first inequality, 'our policy is feasible') together with Corollary B.11, p. 67

import Mathlib
import Definitions.Def_MarkovChain
import Definitions.Def_HubSpokePricing_Lagrangian_Model

namespace HubSpokePricing.Lagrangian

/-- Theorem 4.1, first inequality (p. 17): the Lagrangian policy is feasible for problem (1), so
its stationary average revenue `V^π` (in the original system, Corollary B.11) is at most `V^OPT`
from every initial state in `𝒳`. -/
theorem theorem_4_1_feasible (N : Network) (hN : N.Standing) (lam : ℝ) (hlam : 0 ≤ lam)
    (sol : Fin N.n → SpokeSol N.m) (hsol : ∀ i, SpokeOptimal N lam i (sol i))
    (μ : OrigState N → ℝ) (hμ : MarkovChain.IsStationary (origKernel N sol) μ)
    (x0 : Fin N.n → ℕ) (hx0 : InX N x0) :
    Vpi N sol μ ≤ VOPT N x0 := by sorry

end HubSpokePricing.Lagrangian
