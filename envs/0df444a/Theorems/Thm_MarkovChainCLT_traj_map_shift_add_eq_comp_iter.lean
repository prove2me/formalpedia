-- Prove2me | Theorems.Thm_MarkovChainCLT_traj_map_shift_add_eq_comp_iter
-- name    : MarkovChainCLT.traj_map_shift_add_eq_comp_iter
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T21:03:53.67611+00:00
-- url     : https://prove2.me/theorems/2aa01f98-06d0-4f71-aa84-3f3af5bd1ab5
-- title:
--   Given the past, the chain from time $k+n$ on is started from $P^n(u_k,\cdot)$
-- statement:
--   Let $P$ be a Markov kernel and let $\mathrm{traj}_k$ be the kernel giving the law of the trajectory continuing from an initial segment $u = (u_0,\dots,u_k)$. Then for every $n$,
--
--   $$\bigl(\sigma^{k+n}\bigr)_*\bigl[\mathrm{traj}_k(u)\bigr] \;=\; \int_{\mathsf{X}} \mathbb{P}_y \; P^{n}(u_k,\mathrm{d}y),$$
--
--   where $\sigma^{k+n}\omega = (\omega_{k+n+l})_l$.
--
--   **What it says.** *Conditionally on the first $k+1$ states of the chain, the process observed from time $k+n$ onwards is a chain started from $P^n(u_k,\cdot)$ — and it depends on the conditioning only through $u_k$.* This single statement packages both halves of the Markov property that a mixing estimate needs: **forgetting** (the past enters only via its last state) and **restarting after $n$ steps** (the distribution of that state is $P^n$).
--
--   **Why it is the last probabilistic step.** In the definition of the mixing coefficients $\alpha(n)$, $\rho(n)$, $\phi(n)$ one fixes a split point $k$, a past event in $\sigma(X_0,\dots,X_k)$ and a future event in $\sigma(X_{k+n},X_{k+n+1},\dots)$. Under the identification of the future $\sigma$-algebra as a single pullback along $\sigma^{k+n}$, the conditional probability of the future event given the past is precisely the left-hand side evaluated at a fixed measurable set. This theorem computes it: it equals $\int \mathbb{P}_y(B_0)\,P^n(u_k,\mathrm{d}y)$. Comparing with the stationary value $\int \mathbb{P}_y(B_0)\,\pi(\mathrm{d}y)$ and applying the total-variation bound for $[0,1]$-valued integrands turns any rate $\|P^n(x,\cdot)-\pi\| \le C$ into the bound $\phi(n) \le C$, uniformly in the split point $k$. After this, no probabilistic input remains — only the arithmetic of averages.
--
--   **Proof.** Factor $\sigma^{k+n}$ as $\sigma^{n}\circ\sigma^{k}$, which requires the associativity $k+n+l = k+(n+l)$. The inner shift is handled by the strong restart property, $\sigma^k_*[\mathrm{traj}_k(u)] = \mathbb{P}_{u_k}$; the outer one by the unconditional $n$-step restart, $\sigma^n_*\mathbb{P}_x = \int \mathbb{P}_y P^n(x,\mathrm{d}y)$, after commuting $n+l$ into $l+n$ to match its indexing convention. Composing the two pushforwards with `Measure.map_map` gives the claim.
-- source:
--   C. T. Ionescu Tulcea, "Mesures dans les espaces produits", Atti Accad. Naz. Lincei Rend. 7 (1949) 208-211; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 3 and Ch. 16; C. J. Geyer, "Practical Markov Chain Monte Carlo", Statistical Science 7 (1992) 473-483, Section 3; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Section 3.

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovIterKernel

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal NNReal Topology
open MarkovChainCLT

theorem MarkovChainCLT.traj_map_shift_add_eq_comp_iter {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (k n : ℕ) (u : Π _i : Finset.Iic k, X) :
    (Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) k u).map
        (fun ω : ℕ → X => fun l => ω (k + n + l))
      = (BanditAlgorithm.markovChainKernel P)
          ∘ₘ (iterKernel P n (u ⟨k, Finset.mem_Iic.2 le_rfl⟩)) := by sorry
